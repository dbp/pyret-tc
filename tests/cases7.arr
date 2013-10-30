#lang pyret

data Foo:
  | foo
  | bar
end

cases(Foo) foo:
  | foo => 1
  | bar => "hello"
end