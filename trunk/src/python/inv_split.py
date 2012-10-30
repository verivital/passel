from z3 import *

# bounded model checking applied to Fischer's mutual exclusion protocol
# other examples can be checked by redefining the bad states, initial states, and step and time transition relations appropriately, etc.

# control locations defined as an enumeration datatype
ControlLocation = Datatype('Location')

ControlLocation.declare('idle')
ControlLocation.declare('start')
ControlLocation.declare('check')
ControlLocation.declare('cs')
ControlLocation = ControlLocation.create()

length = 1000 # number of loops to unroll

s = Solver() # instantiate a solver

opt_debug = False

x=[] # list of steps for continuous variable x
q=[] # list of steps for control location
g=[] # list of steps for global variable g

r = Int("r")
i, j, N = Ints("i j N")

delta = Real("delta")

A, B, c, d = Reals("A B c d")
#s.add(A == 1) # safe if A < B; buggy (multiple processes in critical section) if A >= B
#s.add(B == 10)
s.add(And(A > 0, B > 0))
s.add(A < B) # you don't have to pick actual values for A or B

s.add(c == 1)
s.add(d == 2)


Nv = 3 # number of processes

s.add(N == Nv)

reachedList = []
reachedAllList = []


# allocate 1st vars
for k in range(2):
	x.append( [] )
	q.append( [] )
	for i in range(1,Nv+1):
		x[k].append( Real('x' + str(i) + "_" + str(k)) )
		q[k].append( Const( 'q' + str(i) + "_" + str(k), ControlLocation) )
		#s.add( q[k][i-1] == ControlLocation.idle ) # set all other indices to be idle
		s.add( x[k][i-1] >= 0 ) # all processes have nonnegative clocks at all steps
	g.append( Int("g" + str(k)) )
	s.add(And( g[k] >= 0, g[k] <= N) ) # global variable is either a process id 1, ... N, or none of them (0)
	reachedList.append( [ ] ) # append empty list (stores reach sets this direction)

initList = []
# generate initial condition over all processes
for m in range(1,Nv+1):
	initList.append( And( q[0][m-1] == ControlLocation.idle, x[0][m-1] == 0 ) )

initList.append( g[0] == 0 ) # global starts as 0, no process id
if len(initList) > 1:
	init = And( initList )
else:
	init = initList[0]
# quantified version
#init = ForAll([i], Implies(And(i >= 1, i <= N), And( q[0](i) == ControlLocation.idle, x[0](i) == 0, g[0] == 0 ) ) )



k = 0
badList = []
if Nv > 1:
	for m in range(1,Nv+1):
		for n in range(m,Nv+1):
			if n != m:
				badList.append( And( q[k][m-1] == ControlLocation.cs, q[k][n-1] == ControlLocation.cs ) )
else:
	badList.append( q[k][0] == ControlLocation.cs ) # just say reaching cs is bad
if len(badList) > 1:
	bad = Or( badList )
else:
	bad = badList[0]





# split invariant generation
def inv_split(bound):	
	reachedOld = False # no states reached
	reachedOldAll = init
	reachedAll = init
	#reachedAllList.append( reachedAll )
	reached = init
	reachedList[0].append( { "init" : init } )
	
	terminate = 0
	
	# k is the iteration
	for k in range(length):
	
		# allocate new variables lazily / on-the-fly
		km = k + 2
		print "km: " + str(km)
		x.append( Function('x' + str(km), IntSort(), RealSort()) ) # continuous variable
		print x
		q.append( Function('q' + str(km), IntSort(), ControlLocation) ) # control location
		g.append( Int("g" + str(km)) ) # global variable
		s.add(ForAll([i], Implies(i > N, q[km](i) == ControlLocation.idle) )) # set all other indices to be idle
		s.add(ForAll([i], x[km](i) >= 0)) # all processes have nonnegative clocks at all steps
		s.add(And( g[km] >= 0, g[km] <= N) ) # global variable is either a process id 1, ... N, or none of them (0)
		reachedList.append( [] ) # append empty list (stores reach sets this direction)

		if terminate >= 1 or len(reachedList[k]) == 0:
			print "Termination condition reached"
			break
		
		# write bad states in terms of the k^th iteration states
		badList = []
		if Nv > 1:
			for m in range(1,Nv+1):
				for n in range(m,Nv+1):
					if n != m:
						badList.append( And( q[k](m) == ControlLocation.cs, q[k](n) == ControlLocation.cs ) )
		else:
			badList.append( q[k](1) == ControlLocation.cs )
		if len(badList) > 1:
			bad = Or( badList )
		else:
			bad = badList[0]
		
		nt = len(reachedList[k])
		rt = 1
		
		reachedOldAll = reachedAll
		if len(reachedList[k]) > 1:
			#print "REACHEDLIST"
			#print reachedList[k]
			rlist = []
			for ritem in reachedList[k]:
				#print "REACHEDITEM"
				#print ritem
				rlist.append( ritem.items()[0][1] )
			#reachedAll = Or(reachedList[k][0].items()[0][1] )
			reachedAll = Or( rlist )
		else:
			reachedAll = reachedList[k][0].items()[0][1]
		reachedAllList.append( reachedAll )
		#print "RA"
		#print reachedAll
		
		
		if k >= bound - 1:
			print "Terminated without finding a path to bad states after " + str( k ) + " iterations."
			break

		reachedBad = And(reachedAll, bad)
		if opt_debug:
			print reachedBad
			print "\n\n\n"
		s.push() # save context
		s.add(reachedBad)
		result = s.check()
		#print result
		s.pop() # restore context

		if result == sat:
			print "UNSAFE"
			print "Old:\n"
			print reachedOldAll
			print "\nNew:\n"
			print reachedAll
			print "\nBad:\n"
			print reachedBad
			print s.model()
			print "Bad states reached after " + str( k ) + " iterations."
			print bad
			break
		
		if k >= 1:
			s.push() # save context FP
			if opt_debug:
				print "old:\n\n"
				print reachedOldAll
				print "new:\n\n"
				print reachedAll
				print "\n\n\n"
			#fixedPoint = Implies( reachedOldAll, reachedAll )
			#fixedPoint = Implies( reachedAllList[k-1], reachedAllList[k] ) # TODO: this should be the other way, k => k-1, but there's a problem: we need to rename states
			
			#fp = []
			#print reachedAllList[k-1]
			fp = reachedAllList[k-1]
			fpNew = reachedAllList[k]
			for kfp in range(k):
				fp = substitute(fp, (q[kfp](1),q[k](1)), (q[kfp](2),q[k](2)), (x[kfp](1),x[k](1)), (x[kfp](2),x[k](2)), (g[kfp],g[k]) )
				fpNew = substitute(fpNew, (q[kfp](1),q[k](1)), (q[kfp](2),q[k](2)), (x[kfp](1),x[k](1)), (x[kfp](2),x[k](2)), (g[kfp],g[k]) )
			
			#print  reachedAllList[k]
			print fp
			print fpNew
			fixedPoint = Implies( Or(fpNew.children()),  Or(fp.children())) 
			
			
			s.add( Not(fixedPoint) )
			result = s.check()
			s.pop() # restore context FP
		
		for dreached in reachedList[k]:
			#print "ita"
			#print dreached
			reached = dreached.items()[0][1]
			#print reached
			print "k=" + str(k) + " nt=" + str(nt) + " rt=" + str(rt)
			if opt_debug:
				print reached
			
			#if rt == 1 and k >= 2:
			#	print reached
			#	continue
			tnum = 0

			if k >= 1 and result == unsat:# and tnum == 0:
				print "Old:\n"
				print reachedOldAll
				print "\nNew:\n"
				print reachedAll
				print "Fixedpoint:\n"
				print fixedPoint
				terminate = 1
				print "SAFE after " + str(k) + " iterations"
				break
			else:
				#if tnum < 0:
				#	tnum = tnum + 1
				reachedOld = reached
				ts = []
				if k < bound - 1: # termination
					
					goal = Goal()
					tt = timeTransition(k)
					
					# eliminate quantifiers (time elapse variable delta)
					goal.add( tt )
					tac = Tactic('qe')
					r = tac(goal)
					
					if opt_debug:
						print r
					
					#print "KEY"
					#print dreached.keys()[0]
					if dreached.keys()[0] != "t0":
						print "appending time to " + dreached.keys()[0]
						ts.append( simplify(r.as_expr()) )
					
					#ts.append( tt ) # without q.e.

					for iv in range(1,Nv+1):
						ts.extend( stepTransition(k,iv) )
				for t in ts:
					treached = simplify(And(reached, t))
					s.push()
					s.add(treached)
					res = s.check()
					if opt_debug:
						print "transition can be taken? " + str(res)
					s.pop()
					
					#s.push()
					#s.add( Not( Implies( treached, reachedAllList[k] ) ) )
					#resfp = s.check()
					#if resfp == unsat:
					#	print "no new states " + str(resfp)
					#else:
					#	print "NEW STATES"
					#s.pop()
					
					# only explore enabled transitions, no reason to continue down a branch if transitions cannot be taken
					if res == sat:
						key = "t" + str(tnum)
						print key
						tdict = { key : treached }
						reachedList[k+1].append( tdict )
						#print "transition " + str(tnum) + " can be taken? " + str(res)
					tnum = tnum + 1
			rt = rt + 1

	return 0

# transition relation for iteration k of process i 
def stepTransition(k, i):
	ts = []
	
	# idle -> cs (buggy example)
	ts.append(And( q[k][i-1] == ControlLocation.idle, q[k+1][i-1] == ControlLocation.cs, identityTransition(k,i,[q,x],[g]) ) )
	#ts.append(And( q[k][i-1] == ControlLocation.idle, q[k+1][i-1] == ControlLocation.cs, ForAll([j], Implies( And(j >= 1, j <= N, Distinct(i,j)), And( q[k](j) == q[k+1](j), x[k](j) == x[k+1](j), g[k] == g[k+1] ) ) ) ) )
	
	# idle -> start	
	ts.append(And( q[k][i-1] == ControlLocation.idle, g[k] == 0, x[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.start, identityTransition(k,i,[q,x],[g])  ) )
	#ts.append(And( q[k][i-1] == ControlLocation.idle, g[k] == 0, x[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.start, ForAll([j], Implies( And(j >= 1, j <= N, Distinct(i,j)), And( q[k](j) == q[k+1](j), x[k](j) == x[k+1](j), g[k] == g[k+1] ) ) ) ) )
	
	# simpler version
	# start -> idle
	#ts.append(And( q[k][i-1] == ControlLocation.start, g[k] == 0, x[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.idle, identityTransition(k,i,[q,x],[g])  ) )

	# start -> check
	ts.append(And( q[k][i-1] == ControlLocation.start, x[k][i-1] <= A, x[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.check, g[k+1] == i, identityTransition(k,i,[q,x],[])  ) )
	#ts.append(And( q[k][i-1] == ControlLocation.start, x[k][i-1] <= A, x[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.check, g[k+1] == i,          ForAll([j], Implies( And(Distinct(i,j), j >= 1, j <= N), And(q[k](j) == q[k+1](j), x[k](j) == x[k+1](j) )))                ) )
	
	# check -> cs
	ts.append(And( q[k][i-1] == ControlLocation.check, g[k] == i, x[k][i-1] >= B, q[k+1][i-1] == ControlLocation.cs, identityTransition(k,i,[q,x],[g])          ) )
	#ts.append(And( q[k][i-1] == ControlLocation.check, g[k] == i, x[k][i-1] >= B, q[k+1][i-1] == ControlLocation.cs,      ForAll([j], Implies( And(j >= 1, j <= N, Distinct(i,j)), And(q[k](j) == q[k+1](j), x[k](j) == x[k+1](j), g[k] == g[k+1] )))           ) )
	
	# check -> idle
	ts.append(And( q[k][i-1] == ControlLocation.check, g[k] != i, x[k][i-1] >= B, q[k+1][i-1] == ControlLocation.idle, identityTransition(k,i,[q,x],[g])      ) )
	#ts.append(And( q[k][i-1] == ControlLocation.check, g[k] != i, x[k][i-1] >= B, q[k+1][i-1] == ControlLocation.idle,        ForAll([j], Implies( And(j >= 1, j <= N, Distinct(i,j)), And( q[k](j) == q[k+1](j), x[k](j) == x[k+1](j), g[k] == g[k+1] )))               ) )
	
	# cs -> idle
	ts.append(And( q[k][i-1] == ControlLocation.cs, q[k+1][i-1] == ControlLocation.idle, g[k+1] == 0,  identityTransition(k,i,[q,x],[])        ) )
	#ts.append(And( q[k][i-1] == ControlLocation.cs, q[k+1][i-1] == ControlLocation.idle, g[k+1] == 0,        ForAll([j], Implies( And(j >= 1, j <= N, Distinct(i,j) ), And( q[k](j) == q[k+1](j), x[k](j) == x[k+1](j) )))         ) )
	
	return ts

def timeTransition(k):
	# quantified indices version
	#return Exists([delta], And(delta > 0, ForAll([j], And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], x[k+1][j-1] == x[k][j-1] + delta )) ) ) # doesn't respect invariants
	
	ts = []
	for j in range(1,Nv+1):
		# all discrete variables remain unchanged; the last implication enforces the invariant in the start location
		ts.append( And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], x[k+1][j-1] == x[k][j-1] + delta, Implies( (q[k+1][j-1] == ControlLocation.start), x[k+1][j-1] <= A ) ) )
	
	p = Exists([delta], And(delta > 0, And( ts ) ) )
	
	return p

# state identity between states in execution
# i.e., if process 1 makes a discrete transition, assert that the states of process 2 do not change, e.g., q_2 at state k+1 = q_2 at state k
def identityTransition(k,i,lvars,gvars):
	idList = []
	for m in range(1,Nv+1):
		if i != m:
			#p = And( q[k][m-1] == q[k+1][m-1], x[k][m-1] == x[k+1][m-1], g[k] == g[k+1] )
			pl = []
			for lv in lvars:
				pl.append( lv[k][m-1] == lv[k+1][m-1] )
			for gv in gvars:
				pl.append( gv[k] == gv[k+1] )
			if len(pl) > 1:
				p = And( pl )
			else:
				p = pl[0]
			idList.append( p )
	
	if len(idList) == 0:
		idAll = True
	elif len(idList) > 1:
		idAll = And( idList )
	else:
		idAll = idList[0]
	return idAll
	
def allOtherVars(k,i):
	idList = []
	lvars = [q,x]
	gvars = []
	pl = []
	for m in range(1,Nv+1):
		if i != m:
			for lv in lvars:
				pl.append( lv[k][m-1] )
			for gv in gvars:
				pl.append( gv[k] )
	return pl
	

#k = 0
#i = 1

nextIter = initList

for k in range(10):
	# grow variables
	km = k + 2
	x.append( [] )
	q.append( [] )
	for i in range(1,Nv+1):
		x[km].append( Real('x' + str(i) + "_" + str(km)) )
		q[km].append( Const( 'q' + str(i) + "_" + str(km), ControlLocation) )
		s.add( x[km][i-1] >= 0 ) # all processes have nonnegative clocks at all steps
	g.append( Int("g" + str(km)) )
	s.add(And( g[km] >= 0, g[km] <= N) ) # global variable is either a process id 1, ... N, or none of them (0)
	
	print "\n\n\n\n\n\n\n"
	print "ALLOCATED X"
	print x
	print "k = " + str(k)
	
	siList = nextIter
	nextIter = [] # reset for next iteration
	
	
	for i in range(1,Nv+1):
		print "i = " + str(i) + "\n\n"
		splitList = []

		
		for m in range(1,Nv+1):
			# TODO NEXT: iteration K versus iteration 0 ?
			siList.extend( stepTransition(0, m) )
		# TODO: probably want to go ahead and eliminate time variables here, so it's actually the flow statement instead of the time elapse statement
		
		
		
		#siList.append( timeTransition(0) ) # TODO: 0 versus k?
		tgoal = Goal()
		tt = timeTransition(0)

		# eliminate quantifiers (time elapse variable delta)
		tgoal.add( tt )
		ttac = Tactic('qe')
		tr = ttac(tgoal)
		siList.append( simplify(tr.as_expr()) )
		
		
		# TODO NEXT: iteration K versus iteration 0 ?
		print siList[i-1]
		
		splitList.append( Exists(allOtherVars(0,i), Implies(Or(siList), siList[i-1])) ) # careful with siList on 2nd part, was initList
		#print splitList

		goal = Goal()


		print "starting q.e."
		# q.e.
		print splitList
		break
		goal.add( splitList[0] )
		tac = Tactic('qe')
		r = tac(goal)

		print "after q.e."
		#print r
		
		fp = simplify(r.as_expr() )
		
		#kfp = k + 1
		#for j in range(1,Nv+1):
		#	fp = substitute(fp, (q[kfp][j-1],q[k][j-1]), (x[kfp][j-1],x[k][j-1]), (g[kfp],g[k]) )

		nextIter.append( fp )
		#print nextIter
	break
	
	#kfp = k + 1
	fp = Or(siList)
	#for j in range(1,Nv+1):
	#	fp = substitute(fp, (q[kfp][j-1],q[k][j-1]), (x[kfp][j-1],x[k][j-1]), (g[kfp],g[k]) )
	pdList = []
	for pdi in range(0,k):
		for pdj in range(pdi,k):
			if pdi == pdj:
				continue
			pdList.append( Distinct(g[pdi], g[pdj]) )
			for pdp in range(1,Nv+1):
				pdList.append( Distinct(x[pdi][pdp-1], x[pdj][pdp-1]) )
				pdList.append( Distinct(q[pdi][pdp-1], q[pdj][pdp-1]) )
	print pdList
	fpCheck = fp
	if len(pdList) > 0:
		fpCheck = And(fpCheck, And(pdList) )
	
	s.push() # save context
	fpCheck = Implies( Or(nextIter),  fpCheck)
	print fpCheck
	#s.add( Not(fpCheck) )
	s.add( fpCheck )
	res = s.check()
	print "fp check?" + str(res)
	if res == unsat:
		print "FIXED POINT REACHED: " + str(k) + " iterations."
		
		s.push() # save context
		
		safety = Implies( Or(nextIter), Not( Or( badList ) ))
		s.add( Not(safety) )
		sres = s.check()
		print "safety check?" + str(res)
		
		s.pop() # restore context
		
		print "invariant:"
		for kfp in range(0,k):
			for j in range(1,Nv+1):
				fp = substitute(fp, (q[kfp][j-1],q[0][j-1]), (x[kfp][j-1],x[0][j-1]), (g[kfp],g[0]) )
		print simplify(fp)
		print "next inv:"
		print nextIter
		
		
		break
	s.pop() # restore context


# call BMC for length iterations
#inv_split(length)


