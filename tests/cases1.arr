#lang pyret

#! value in cases expression should have type Foo

data Foo:
  | foo
  | bar
end

data Baz:
  | baz
end

cases(Foo) baz:
  | foo => 1
  | bar => 2
end