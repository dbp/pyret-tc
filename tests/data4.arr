#lang pyret

data Foo:
  | a(x)
  | b(y)
end

fun f(c :: Foo):
  f
end

f(a(10))

f(b(true))