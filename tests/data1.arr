#lang pyret

#! 1st argument was expected to be of type Foo, but was the incompatible type Bar

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