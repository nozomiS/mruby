#include <mruby.h>
#include <mruby/class.h>
#include <mruby/compile.h>
#include <mruby/irep.h>
#include <mruby/proc.h>
#include <mruby/opcode.h>
#include <stdbool.h>

static unsigned int
__capture_lvs(mrb_state *mrb, mrbc_context *cxt, struct REnv *env, bool pretend)
{
  mrb_sym *syms = cxt->syms;
  mrb_value *stack = mrb->c->stack + 1; /* All stack[0]s are belong to receiver */
  unsigned int slen = 0;

  while (env) {
    struct RProc *proc;
    mrb_irep *irep;

    if (!MRB_ENV_STACK_SHARED_P(env)) {
      break;
    }

    proc = mrb->c->cibase[env->cioff].proc;
    if (!proc || MRB_PROC_CFUNC_P(proc)) {
      break;
    }

    irep = proc->body.irep;
    if (!irep || irep->nlocals < 1) {
      break;
    }

    if (!pretend && syms) {
      int i;
      for (i = 0; i < irep->nlocals - 1; i++) {
        *syms++ = irep->lv[i].name;
        *stack++ = env->stack[irep->lv[i].r];
      }
    }

    slen += irep->nlocals - 1;

    env = (struct REnv *)env->c;
  }

  return slen;
}

static unsigned int
capture_lvs(mrb_state *mrb, mrbc_context *cxt, struct REnv *env)
{
  unsigned int slen;
  slen = __capture_lvs(mrb, cxt, env, true) + 1; /* 1 is for receiver */

  mrb_stack_extend(mrb, slen, slen);

  cxt->syms = (mrb_sym *)mrb_realloc(mrb, cxt->syms, slen * sizeof(mrb_sym));
  cxt->slen = slen;

  /* collect them */
  __capture_lvs(mrb, cxt, env, false);

  return slen;
}

void mrb_codedump_all(mrb_state*, struct RProc*);

static struct RProc*
create_proc_from_string(mrb_state *mrb, char *s, int len, mrb_value binding, const char *file, mrb_int line, unsigned int *slen)
{
  mrbc_context *cxt;
  struct mrb_parser_state *p;
  struct RProc *proc;
  struct mrb_context *c = mrb->c;

  if (!mrb_nil_p(binding)) {
    mrb_raise(mrb, E_ARGUMENT_ERROR, "Binding of eval must be nil.");
  }

  cxt = mrbc_context_new(mrb);
  cxt->lineno = line;

  if (!file) {
    file = "(eval)";
  }
  mrbc_filename(mrb, cxt, file);
  cxt->capture_errors = TRUE;

  /* capture variables in envs */
  if (slen) {
    mrb_callinfo *prev_ci = &c->ci[-1];
    struct REnv *env = prev_ci->proc->env;

    if (!MRB_PROC_CFUNC_P(prev_ci->proc)) {
      env = (struct REnv *)mrb_obj_alloc(mrb, MRB_TT_ENV, (struct RClass *)env);
      env->mid = prev_ci->mid;
      env->cioff = prev_ci - c->cibase;
      env->stack = c->ci->stackent;
      MRB_SET_ENV_STACK_LEN(env, prev_ci->proc->body.irep->nlocals);
      c->ci->env = env;
    }
    *slen = capture_lvs(mrb, cxt, env);
  }

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

  if (c->ci[-1].proc->target_class) {
    proc->target_class = c->ci[-1].proc->target_class;
  }
  proc->env = c->ci->env;

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
  unsigned int keep = 0;

  mrb_get_args(mrb, "s|ozi", &s, &len, &binding, &file, &line);

  proc = create_proc_from_string(mrb, s, len, binding, file, line, &keep);
  ret = mrb_top_run(mrb, proc, mrb->c->stack[0], keep);
  if (mrb->exc) {
    mrb_exc_raise(mrb, mrb_obj_value(mrb->exc));
  }

  /* TODO: maybe need to writeback to env's stack from the stack */

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
    proc = create_proc_from_string(mrb, s, len, mrb_nil_value(), file, line, NULL);
    mrb->c->ci->env = NULL;
    return mrb_vm_run(mrb, proc, mrb->c->stack[0], 0);
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
}

void
mrb_mruby_eval_gem_final(mrb_state* mrb)
{
}
