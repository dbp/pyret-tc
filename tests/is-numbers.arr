#lang pyret

fun add1(n :: Number) -> Number:
  10
end

fun f(x):
  add1(x)
where:
  f("Fo") is 10
end