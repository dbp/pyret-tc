all:
	raco make tc.arr

test: all
	raco pyret tc-unit.arr
	raco pyret tc-test.arr
