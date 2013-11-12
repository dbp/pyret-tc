#lang pyret

#! Found branches with incompatible types: Number, String.

data Foo:
  | foo
  | bar
end

cases(Foo) foo:
  | foo => 1
  | bar => "hello"
end