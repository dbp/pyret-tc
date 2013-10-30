#lang pyret

data Foo:
  | foo
end

data Bar:
  | bar
end

fun foo-something(f :: Foo) -> Foo:
  f
end

foo-something(bar)