#lang pyret

#! 1st argument was expected to be of type (String -> Nothing), but was the incompatible type (Number -> Nothing)

x :: List<String> = ["Foo"]

fun f(y :: Number) -> Nothing:
  nothing
end

x.each(f)