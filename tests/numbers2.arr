#lang pyret

#! body of the function has type String, which is incompatible with the return type specified in annotations as Number

fun f(x :: Number) -> Number:
  x.tostring()
end