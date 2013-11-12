#lang pyret

#! 1st argument was expected to be of type Option<String>, but was the incompatible type Option<Number>

fun foo(x :: Option<String>):
  nothing
end

foo(some(19))