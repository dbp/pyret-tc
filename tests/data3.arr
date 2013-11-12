#lang pyret

#! 1st argument was expected to be of type Number, but was the incompatible type String

data Foo:
  | bar(a :: Number)
end

bar("foo")