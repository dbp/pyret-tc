#lang pyret

#==

data Foo:
  | foo
  | bar
  | baz
end

cases(Foo) foo:
  | bar => 1
  | baz => 2
  | foo => 3
end