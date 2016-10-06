#include <mruby.h>
#include <mruby/class.h>
#include <mruby/irep.h>
#include <mruby/proc.h>
#include <mruby/data.h>
#include <mruby/array.h>
#include <mruby/variable.h>

#define ARG_MAX 127

struct scope {
  struct REnv *env;

  struct mrb_locals *lv;
  mrb_int lv_len;
};

struct binding_context {
  struct scope *scopes;
  mrb_int scopes_len;

  mrb_value receiver;
  mrb_value target_class;

  struct mrb_locals additiona_lv[ARG_MAX];
};

static void
mrb_binding_dfree(mrb_state *mrb, void *ptr)
{
  struct binding_context *bcxt = (struct binding_context *)ptr;
  if (bcxt) {
    mrb_int i;
    for (i = 0; i < bcxt->scopes_len; i++) {
      struct scope *s = &bcxt->scopes[i];
      /* s->env will be sweeped */

      if (i != 0) {
        mrb_free(mrb, s->lv);
      }
    }
    mrb_free(mrb, bcxt->scopes);
  }
  mrb_free(mrb, ptr);
}

static mrb_data_type binding_data_type = {
  .struct_name = "Binding context",
  .dfree = mrb_binding_dfree,
};


static mrb_irep *
get_closure_irep(mrb_state *mrb, struct REnv *env) {
  struct RProc *proc;
  mrb_irep *irep;

  if (!MRB_ENV_STACK_SHARED_P(env)) {
    /* skip it because non shared env has special cioff */
    return NULL;
  }

  proc = mrb->c->cibase[env->cioff].proc;
  if (!proc || MRB_PROC_CFUNC_P(proc)) {
    /* cfunc has neither local variable and related symbol */
    return NULL;
  }

  irep = proc->body.irep;
  if (!irep || irep->nlocals < 1) {
    return NULL;
  }

  return irep;
}

static struct REnv *
insert_callers_env(mrb_state *mrb, int depth) {
  mrb_callinfo *prev_ci;
  struct REnv *env;
  struct mrb_context *cxt = mrb->c;

  //dump_ci(mrb);
  prev_ci = &cxt->ci[depth];
  env = prev_ci->proc->env;
  if (!env) {
    env = prev_ci->env;
  }
  env = (struct REnv *)mrb_obj_alloc(mrb, MRB_TT_ENV, (struct RClass *)env);

  env->mid = prev_ci->mid;
  if (MRB_PROC_CFUNC_P(prev_ci->proc)) {
    MRB_ENV_UNSHARE_STACK(env);
    env->stack = mrb_malloc(mrb, sizeof(mrb_value));
    *env->stack = *cxt->ci[depth + 1].stackent;
    MRB_SET_ENV_STACK_LEN(env, 1);
  } else {
    env->cioff = prev_ci - cxt->cibase;
    env->stack = cxt->ci[depth + 1].stackent;
    MRB_SET_ENV_STACK_LEN(env, prev_ci->proc->body.irep->nlocals);
  }

  return env;
}

static mrb_int
get_env_levels(const struct REnv *env)
{
  mrb_int level = 0;
  while (env) {
    level++;
    env = (const struct REnv *)env->c;
  }
  return level;
}

static mrb_int
get_callers_depth(mrb_state *mrb)
{
  mrb_int depth = 0;
  ptrdiff_t delta;
  struct mrb_context *cxt = mrb->c;

  mrb_get_args(mrb, "|i", &depth);

  delta = cxt->ci - cxt->cibase;
  if (delta < depth) {
    mrb_raise(mrb, E_ARGUMENT_ERROR, "depth is too deep");
  }

  return (-depth - 1);
}

static void
setup_scopes(mrb_state *mrb, struct binding_context *bcxt, struct REnv *env, mrb_value catcher)
{
  struct scope *s;

  /* create a virtual env for additional local variable space */
  s = &bcxt->scopes[0];
  s->env = (struct REnv *)mrb_obj_alloc(mrb, MRB_TT_ENV, (struct RClass *)env);
  s->env->mid = 0;
  MRB_ENV_UNSHARE_STACK(s->env);
  s->env->stack = mrb_malloc(mrb, sizeof(mrb_value) * ARG_MAX);
  s->env->stack[0] = mrb_nil_value(); /* dummy R0 */
  MRB_SET_ENV_STACK_LEN(s->env, 1);

  s->lv = &bcxt->additiona_lv[0];
  s->lv_len = 0;
  mrb_ary_push(mrb, catcher, mrb_obj_value(s->env));

  /* get the flatten envs */
  s = &bcxt->scopes[1];
  while (env) {
    mrb_irep *irep = get_closure_irep(mrb, env);
    if (irep) {
      s->lv_len = irep->nlocals > 0 ? irep->nlocals - 1 : 0;
      s->lv = mrb_malloc(mrb, sizeof(struct mrb_locals) * s->lv_len);
      if (s->lv && irep->lv) {
        int i;
        for (i = 0; i < s->lv_len; i++) {
          s->lv[i] = irep->lv[i];
        }
      }
    }

    s->env = env;
    mrb_ary_push(mrb, catcher, mrb_obj_value(env));

    s++;
    env = (struct REnv *)env->c;
  }
}

static mrb_value
mrb_binding_initialize(mrb_state *mrb, mrb_value self)
{
  mrb_value catcher;
  mrb_callinfo *prev_ci;
  int depth;
  struct REnv *env;
  struct binding_context *bcxt = mrb_malloc(mrb, sizeof(struct binding_context));

  mrb_data_init(self, bcxt, &binding_data_type);

  /* measure depth and create context */
  depth = get_callers_depth(mrb);

  env = insert_callers_env(mrb, depth);
  bcxt->scopes_len = get_env_levels(env) + 1; /* +1 is for virtual */

  bcxt->scopes = (struct scope *)mrb_malloc(mrb, sizeof(struct scope) * bcxt->scopes_len);
  memset(bcxt->scopes, 0, sizeof(struct scope) * bcxt->scopes_len);

  /* create a catcher to catch all relative objects */
  catcher = mrb_ary_new_capa(mrb, bcxt->scopes_len + 2);
  mrb_iv_set(mrb, self, mrb_intern_lit(mrb, "__catcher__"), catcher);

  /* collect local variables */
  setup_scopes(mrb, bcxt, env, catcher);

  /* save the R0(receiver) since it will be destroyed */
  bcxt->receiver = bcxt->scopes[1].env->stack[0];
  mrb_ary_push(mrb, catcher, bcxt->receiver);

  /* save the target_class */
  prev_ci = &mrb->c->ci[depth];
  if (prev_ci->target_class) {
    bcxt->target_class = mrb_obj_value(prev_ci->target_class);
    mrb_ary_push(mrb, catcher, bcxt->target_class);
  } else {
    bcxt->target_class = mrb_nil_value();
  }

  return self;
}

static mrb_value
mrb_binding_eval(mrb_state *mrb, mrb_value self)
{
  struct binding_context *cxt = DATA_PTR(self);
  mrb_int argc;
  mrb_value argv[4]; /* arg order is string, binding, filename, lineno */
  argv[1] = self;
  argv[2] = argv[3] = mrb_nil_value();

  argc = mrb_get_args(mrb, "o|oo", &argv[0], &argv[2], &argv[3]);
  if (argc < 1 || !mrb_string_p(argv[0])) {
    mrb_raise(mrb, E_ARGUMENT_ERROR, "a string required at least");
  }

  if (cxt->scopes_len < 2) {
    mrb_raise(mrb, E_RUNTIME_ERROR, "expected receiver missed");
  }

  return mrb_funcall_argv(mrb, cxt->receiver, mrb_intern_lit(mrb, "eval"), 4, &argv[0]);
}

static mrb_value
binding_lv_get(mrb_state *mrb, mrb_value self)
{
  mrb_sym sym = 0;
  struct binding_context *cxt = DATA_PTR(self);
  mrb_int i;

  mrb_get_args(mrb, "n", &sym);
  if (sym == 0) {
    mrb_raise(mrb, E_ARGUMENT_ERROR, "invalid symbol");
  }

  for (i = cxt->scopes_len - 1; i >= 0; i--) {
    struct scope *s = &cxt->scopes[i];
    mrb_int j;

    for (j = 0; j < s->lv_len; j++) {
      if (s->lv[j].name == sym) {
        return s->env->stack[s->lv[j].r];
      }
    }
  }

  mrb_name_error(mrb, sym, "local variable `%S' not defined for %S",
                   mrb_sym2str(mrb, sym), self);

  return mrb_nil_value();
}

static mrb_value
mrb_binding_lv_defined_p(mrb_state *mrb, mrb_value self)
{
  mrb_value result = binding_lv_get(mrb, self);

  return mrb_bool_value(mrb_nil_p(result));
}

static mrb_value
mrb_binding_lv_get(mrb_state *mrb, mrb_value self)
{
  mrb_value result = binding_lv_get(mrb, self);

  return result;
}

static mrb_value
mrb_binding_lv_set(mrb_state *mrb, mrb_value self)
{
  struct scope *s;
  mrb_sym sym = 0;
  mrb_value obj = mrb_nil_value();
  struct binding_context *cxt = DATA_PTR(self);
  mrb_int i;

  mrb_get_args(mrb, "no", &sym, &obj);
  if (sym == 0) {
    mrb_raise(mrb, E_ARGUMENT_ERROR, "invalid symbol");
  }

  /* try to find the sym from captured scopes */
  for (i = 0; i < cxt->scopes_len; i++) {
    struct scope *s = &cxt->scopes[i];
    mrb_int j;

    for (j = 0; j < s->lv_len; j++) {
      if (s->lv[j].name == sym) {
        mrb_value replaced = s->env->stack[s->lv[j].r];
        if (!mrb_obj_eq(mrb, replaced, obj)) {
          s->env->stack[s->lv[j].r] = obj;
          mrb_field_write_barrier_value(mrb, mrb_basic_ptr(self), obj);
        }
        return obj;
      }
    }
  }

  /* new sym arrives */
  if (cxt->scopes[0].lv_len >= ARG_MAX) {
    return mrb_nil_value(); /* overflow, need to call hell raiser? */
  }

  s = &cxt->scopes[0];
  s->lv[s->lv_len].name = sym;
  s->lv[s->lv_len].r = s->lv_len;
  s->env->stack[s->lv_len] = obj;
  mrb_field_write_barrier_value(mrb, mrb_basic_ptr(self), obj);

  /* update stored length */
  s->lv_len++;
  MRB_SET_ENV_STACK_LEN(s->env, MRB_ENV_STACK_LEN(s->env) + 1);

  return obj;
}

static mrb_value
mrb_binding_lvs(mrb_state *mrb, mrb_value self)
{
  mrb_value ary = mrb_ary_new(mrb);
  struct binding_context *bcxt = DATA_PTR(self);
  mrb_int i;
  int ai = mrb_gc_arena_save(mrb);

  for (i = 0; i < bcxt->scopes_len; i++) {
    struct scope *s = &bcxt->scopes[i];
    mrb_int j;

    for (j = 0; j < s->lv_len; j++) {
      if (!s->lv[j].name) {
        continue;
      }
      mrb_ary_push(mrb, ary, mrb_symbol_value(s->lv[j].name));
      mrb_gc_arena_restore(mrb, ai);
    }
  }

  return ary;
}

static mrb_value
mrb_binding_receiver(mrb_state *mrb, mrb_value self)
{
  struct binding_context *bcxt = DATA_PTR(self);

  return bcxt->receiver;
}

static mrb_value
mrb_f_binding(mrb_state *mrb, mrb_value self)
{
  mrb_value argv = mrb_fixnum_value(1);

  return mrb_obj_new(mrb, mrb_class_get(mrb, "Binding"), 1, &argv);
}

static void
mrb_mruby_binding_init(mrb_state *mrb)
{
  struct RClass *c = mrb_define_class(mrb, "Binding", mrb->object_class);
  MRB_SET_INSTANCE_TT(c, MRB_TT_DATA);

  mrb_define_method(mrb, c, "initialize", mrb_binding_initialize, MRB_ARGS_NONE());
  mrb_define_method(mrb, c, "eval", mrb_binding_eval, MRB_ARGS_ARG(1, 2));
  mrb_define_method(mrb, c, "local_variable_defined?", mrb_binding_lv_defined_p, MRB_ARGS_REQ(1));
  mrb_define_method(mrb, c, "local_variable_get", mrb_binding_lv_get, MRB_ARGS_NONE());
  mrb_define_method(mrb, c, "local_variable_set", mrb_binding_lv_set, MRB_ARGS_REQ(1));
  mrb_define_method(mrb, c, "local_variables", mrb_binding_lvs, MRB_ARGS_NONE());
  mrb_define_method(mrb, c, "receiver", mrb_binding_receiver, MRB_ARGS_NONE());

  mrb_define_module_function(mrb, mrb->kernel_module, "binding", mrb_f_binding, MRB_ARGS_NONE());
}

/*******************************************************************/

static void
writeback_lvs_to_scopes(mrb_state *mrb, struct binding_context *bcxt)
{
  struct scope *s = &bcxt->scopes[0];
  const mrb_value *sstack = mrb->c->stack + 1;
  mrb_int i;

  for (i = 0; i < bcxt->scopes_len; i++, s++) {
    mrb_value *dstack = s->env->stack;
    mrb_int j;

    for (j = 0; j < s->lv_len; j++) {
      if (s->lv[j].name) {
         dstack[s->lv[j].r] = *sstack++;
      }
    }
  }
}

static unsigned int
__push_lvs_to_mstack(mrb_state *mrb, mrbc_context *cxt, struct binding_context *bcxt, mrb_bool pretend) {
  mrb_sym *syms = cxt->syms;
  struct scope *s = &bcxt->scopes[0];
  mrb_value *dstack = s->env->stack + s->lv_len + 1;
  unsigned int slen = 0;
  mrb_int i;

  for (i = 0; i < bcxt->scopes_len; i++, s++) {
    const mrb_value *sstack = s->env->stack;
    mrb_int j;

    for (j = 0; j < s->lv_len; j++) {
      if (!s->lv[j].name) {
        continue;
      }

      slen++;

      if (!pretend) {
        *syms++ = s->lv[j].name;
        if (i != 0) { /* virtual env is already taken up */
          *dstack++ = sstack[s->lv[j].r];
        }
      }
    }
  }

  return slen;
}

static unsigned int
push_lvs_to_mstack(mrb_state *mrb, mrbc_context *cxt, struct binding_context *bcxt)
{
  struct scope *s = &bcxt->scopes[0];
  /* just get the required stack length */
  unsigned int slen = __push_lvs_to_mstack(mrb, cxt, bcxt, TRUE);

  mrb->c->ci->env = s->env;
  s->env->stack = mrb_realloc(mrb, s->env->stack,
                            sizeof(mrb_value) * (slen + 2));

  cxt->syms = (mrb_sym *)mrb_realloc(mrb, cxt->syms, sizeof(mrb_sym) * slen);
  cxt->slen = slen;

  __push_lvs_to_mstack(mrb, cxt, bcxt, FALSE);

  return slen + 1;
}

void mrb_codedump_all(mrb_state*, struct RProc*);

static mrb_value
dummy_func(mrb_state *mrb, mrb_value self)
{
  return mrb_nil_value();
}

// what an ugly implementation. but i have no way except this...
static void set_args(mrb_state *mrb, mrb_int argc, mrb_value *argv,
              struct binding_context *bcxt)
{
  int nregs = mrb->c->ci->nregs;
  mrb_value dummy_proc = mrb_obj_value(mrb_proc_new_cfunc(mrb, dummy_func));

  mrb->c->ci->nregs = 0;
  mrb_yield_with_class(mrb, dummy_proc, argc, argv,
                   bcxt->receiver, mrb->object_class);
  mrb->c->ci->nregs = nregs;
}


static struct RProc*
create_proc_from_string(mrb_state *mrb, char *s, int len, mrb_value binding, const char *file, mrb_int line)
{
  mrbc_context *cxt;
  struct mrb_parser_state *p;
  struct RProc *proc;
  struct REnv *env = NULL;
  struct binding_context *bcxt = NULL;

  if (mrb_nil_p(binding)) {
    mrb_value argv = mrb_fixnum_value(1);

    binding = mrb_obj_new(mrb, mrb_class_get(mrb, "Binding"), 1, &argv);
  }
  else if (mrb_type(binding) != MRB_TT_DATA) { // XXX need more check
    mrb_raise(mrb, E_ARGUMENT_ERROR, "invalid type of binding");
  }

  bcxt = (struct binding_context *)DATA_PTR(binding);

  cxt = mrbc_context_new(mrb);
  cxt->lineno = line;

  if (!file) {
    file = "(eval)";
  }
  mrbc_filename(mrb, cxt, file);
  cxt->capture_errors = TRUE;

  /* capture variables in envs */
  push_lvs_to_mstack(mrb, cxt, bcxt);

  p = mrb_parse_nstring(mrb, s, len, cxt);
  /* only occur when memory ran out */
  if (!p) {
    mrb_raise(mrb, E_RUNTIME_ERROR, "Failed to create parser state.");
  }

  if (0 < p->nerr) {
    /* parse error */
    char buf[256];
    int n;
    n = snprintf(buf, sizeof(buf), "line %d: %s\n", p->error_buffer[0].lineno, p->error_buffer[0].message);
    mrb_parser_free(p);
    mrbc_context_free(mrb, cxt);
    mrb_exc_raise(mrb, mrb_exc_new(mrb, E_SYNTAX_ERROR, buf, n));
  }

  proc = mrb_generate_code(mrb, p);
  mrb_parser_free(p);
  mrbc_context_free(mrb, cxt);

  if (proc == NULL) {
    /* codegen error */
    mrb_raise(mrb, E_SCRIPT_ERROR, "codegen error");
  }

  /* mrb_codedump_all(mrb, proc); */

  proc->env = env;

  set_args(mrb, proc->body.irep->nlocals,
                 bcxt->scopes[0].env->stack + 1, bcxt);

  return proc;
}

static mrb_value
f_eval(mrb_state *mrb, mrb_value self)
{
  char *s;
  mrb_int len;
  mrb_value binding = mrb_nil_value();
  char *file = NULL;
  mrb_int line = 1;
  mrb_value ret;
  struct RProc *proc;
  struct binding_context *bcxt;

  mrb_get_args(mrb, "s|ozi", &s, &len, &binding, &file, &line);
  if (mrb_nil_p(binding)) {
    mrb_value argv = mrb_fixnum_value(1);

    binding = mrb_obj_new(mrb, mrb_class_get(mrb, "Binding"), 1, &argv);
  }
  else if (mrb_type(binding) != MRB_TT_DATA) { // XXX need more check
    mrb_raise(mrb, E_ARGUMENT_ERROR, "invalid type of binding");
  }

  proc = create_proc_from_string(mrb, s, len, binding, file, line);

  bcxt = (struct binding_context *)DATA_PTR(binding);
  if (bcxt && !mrb_nil_p(bcxt->target_class)) {
    proc->target_class = mrb_class_ptr(bcxt->target_class);
  }

  ret = mrb_top_run(mrb, proc, bcxt->receiver, proc->body.irep->nlocals);
  if (mrb->exc) {
    mrb_exc_raise(mrb, mrb_obj_value(mrb->exc));
  }

  writeback_lvs_to_scopes(mrb, bcxt);

  return ret;
}

mrb_value mrb_obj_instance_eval(mrb_state *mrb, mrb_value self);

#define CI_ACC_SKIP    -1

static mrb_value
f_instance_eval(mrb_state *mrb, mrb_value self)
{
  struct mrb_context *c = mrb->c;
  mrb_value b;
  mrb_int argc; mrb_value *argv;

  mrb_get_args(mrb, "*&", &argv, &argc, &b);

  if (mrb_nil_p(b)) {
    char *s;
    mrb_int len;
    char *file = NULL;
    mrb_int line = 1;
    mrb_value cv;
    struct RProc *proc;

    mrb_get_args(mrb, "s|zi", &s, &len, &file, &line);
    c->ci->acc = CI_ACC_SKIP;
    cv = mrb_singleton_class(mrb, self);
    c->ci->target_class = mrb_class_ptr(cv);

    proc = create_proc_from_string(mrb, s, len, mrb_nil_value(), file, line);
    c->ci->env = NULL;
    return mrb_vm_run(mrb, proc, self, proc->body.irep->nlocals);
  }
  else {
    mrb_get_args(mrb, "&", &b);
    return mrb_obj_instance_eval(mrb, self);
  }
}

void
mrb_mruby_eval_gem_init(mrb_state* mrb)
{
  mrb_define_module_function(mrb, mrb->kernel_module, "eval", f_eval, MRB_ARGS_ARG(1, 3));
  mrb_define_method(mrb, mrb->kernel_module, "instance_eval", f_instance_eval, MRB_ARGS_ARG(1, 2));

  mrb_mruby_binding_init(mrb);
}

void
mrb_mruby_eval_gem_final(mrb_state* mrb)
{
}
