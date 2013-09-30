#lang pyret

import pyret-eval as E
import ast as A
import directory as D
import file as F

# micro helpers
fun Stx(in):
  A.Program(in) or A.Expr(in)
end

# Template for structural recursion
# cases(A.Expr) get-expr(ast):
#   | s_block(l, stmts) =>
#   | s_user_block(l, block) =>
#   | s_var(l, name, val) =>
#   | s_let(l, name, val) =>
#   | s_assign(l, id, val) =>
#   | s_if(l, branches) =>
#   | s_lam(l, ps, args, ann, doc, body, ck) =>
#   | s_method(l, args, ann, doc, body, ck) =>
#   | s_extend(l, super, fields) =>
#   | s_update(l, super, fields) =>
#   | s_obj(l, fields) =>
#   | s_app(r, fn, args) =>
#   | s_id(l, id) =>
#   | s_num(l, num) =>
#   | s_bool(l, bool) =>
#   | s_str(l, str) =>
#   | s_get_bang(l, obj, str) =>
#   | s_bracket(l, obj, field) =>
#   | s_colon_bracket(l, obj, field) =>
# end

fun tc-prog(prog :: A.Program, env):
  A.s_program(prog.l, prog.imports, tc(prog.block, env))
end

fun tc(ast :: A.Expr, env):
  cases(A.Expr) ast:
    | s_block(l, stmts) => ast
    | s_user_block(l, block) => ast
    | s_var(l, name, val) => ast
    | s_let(l, name, val) => ast
    | s_assign(l, id, val) => ast
    | s_if(l, branches) => ast
    | s_lam(l, ps, args, ann, doc, body, ck) => ast
    | s_method(l, args, ann, doc, body, ck) => ast
    | s_extend(l, super, fields) => ast
    | s_update(l, super, fields) => ast
    | s_obj(l, fields) => ast
    | s_app(r, fn, args) => ast
    | s_id(l, id) => ast
    | s_num(l, num) => ast
    | s_bool(l, bool) => ast
    | s_str(l, str) => ast
    | s_get_bang(l, obj, str) => ast
    | s_bracket(l, obj, field) => ast
    | s_colon_bracket(l, obj, field) => ast
  end
end



# basic testing harness
fun build-path(parts):
  parts.join-str("/")
end
fun str-ends-with(s1,s2):
  s1.substring(s1.length() - s2.length(), s1.length()) == s2
end
fun str-starts-with(s1,s2):
  s1.substring(0, s2.length()) == s2
end
fun strip-ext(s):
  s.substring(0, s.length() - 4)
end

fun is-code-file(path):
  path^str-ends-with(".arr") and (not path^str-starts-with("."))
end

fun eval-str(p, s):
  default-env = {list: list, error: error}
  prog = s^A.parse(p, { ["check"]: false}).post-desugar^tc-prog({})
  E.eval(prog^A.to-native(), default-env, {})
end

D.dir("tests").list().map(fun(path):
    when is-code-file(path):
      # NOTE(dbp 2013-09-29):
      # We run the .arr file. It expects to have a corresponding .out and .err files.
      # if .err is non-empty, we expect to see an error that matches the content of that
      # file. If it is empty, we expect the value that comes out of the .arr to match the
      # value that comes from the .out. Obviously, the .out files should be much simpler than
      # the .arr files.
      outpath = strip-ext(path) + ".out"
      errpath = strip-ext(path) + ".err"
      code = F.input-file(build-path(["tests", path])).read-file()
      out = F.input-file(build-path(["tests", outpath])).read-file()
      err = F.input-file(build-path(["tests", errpath])).read-file()
      check:
        if err.length() <> 0:
          eval-str(path, code) raises err
        else:
          eval-str(path, code) is eval-str(outpath, out)
        end
      end
    end
  end)