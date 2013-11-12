#lang pyret

#! 1st argument was expected to be of type Number, but was the incompatible type String

fun f(a :: Number) -> Number:
  a
end

f("foo")