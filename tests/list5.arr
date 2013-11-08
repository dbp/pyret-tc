#lang pyret

x :: List<String> = ["Foo"]

fun f(y :: Number) -> Nothing:
  nothing
end

x.each(f)