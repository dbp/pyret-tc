#lang pyret

import pyret-eval as E
import ast as A
import directory as D
import file as F


# basic testing harness
fun build-path(parts):
  parts.join-str("/")
end

fun str-ends-with(s1,s2):
  s1.substring(s1.length() - s2.length(), s1.length()) == s2
end

fun strip-ext(s):
  s.substring(0, s.length() - 4)
end

fun is-code-file(path):
  path^str-ends-with(".arr")
end

fun eval-str(p, s):
  prog = s^A.parse(p, { ["check"]: false}).pre-desugar^A.to-native()
  E.eval(prog, {}, {})
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