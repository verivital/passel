from z3 import *
from sets import Set
import time
from datetime import *

# control locations defined as an enumeration datatype
ControlLocation = Datatype('Location')

fischer = 0
mux = 1
fischer_aux = 2
pmode = fischer


set_option(max_depth=1000)
set_option(max_lines=1000)
set_option(pp_min_alias_size=1000) # doesn't work, at least not for .sexpr()

ControlLocation.declare('idle')
ControlLocation.declare('start')
if pmode == fischer or pmode == fischer_aux:
	ControlLocation.declare('check')
ControlLocation.declare('cs')
ControlLocation = ControlLocation.create()

s = Solver() # instantiate a solver


q=[] # list of steps for control location
if pmode == fischer or pmode == fischer_aux:
	x=[] # list of steps for continuous variable x
	g=[] # list of steps for global variable g
if pmode == fischer_aux:
	last=[]
	first=[]
if pmode == mux:
	gx=[]

r = Int("r")
i, j, N = Ints("i j N")

if pmode == fischer or pmode == fischer_aux:
	t1 = Real("t1") # time elapse variable

	A, B, c, d = Reals("A B c d")
	#s.add(A == 1) # safe if A < B; buggy (multiple processes in critical section) if A >= B
	#s.add(B == 10)
	s.add(And(A > 0, B > 0))
	s.add(A < B) # you don't have to pick actual values for A or B
	s.add(A == 5)
	s.add(B == 7)

	#s.add(c == 1) # unused for now
	#s.add(d == 2)


Nv = 3 # number of processes

s.add(N >= Nv)


# allocate 1st vars
for k in range(2):
	if pmode == fischer or pmode == fischer_aux:
		x.append( [] )
	if pmode == fischer_aux:
		last.append( [] )
		first.append( [] )
	q.append( [] )
	for i in range(1,Nv+1):
		q[k].append( Const( 'q' + str(i) + "_" + str(k), ControlLocation) )
		if pmode == fischer or pmode == fischer_aux:
			x[k].append( Real('x' + str(i) + "_" + str(k)) )
			s.add( x[k][i-1] >= 0 ) # all processes have nonnegative clocks at all steps
		if pmode == fischer_aux:
			last[k].append( Real('last' + str(i) + "_" + str(k)) )
			first[k].append( Real('first' + str(i) + "_" + str(k)) )
			s.add( last[k][i-1] >= 0 ) # all processes have nonnegative clocks at all steps
			s.add( first[k][i-1] >= 0 ) # all processes have nonnegative clocks at all steps
	if pmode == fischer or pmode == fischer_aux:
		g.append( Int("g" + str(k)) )
		s.add(And( g[k] >= 0, g[k] <= N) ) # global variable is either a process id 1, ... N, or none of them (0)
	if pmode == mux:
		gx.append( Int("gx" + str(k)) )
		s.add(And( gx[k] >= 0, gx[k] <= 1) ) # global variable is a bit

initList = []
# generate initial condition over all processes
for m in range(1,Nv+1):
	if pmode == fischer or pmode == fischer_aux:
		initList.append( x[0][m-1] == 0 )
	if pmode == fischer_aux:
		initList.append( last[0][m-1] == A )
		initList.append( first[0][m-1] == 0 )
	initList.append( And( q[0][m-1] == ControlLocation.idle ) )

if pmode == fischer or pmode == fischer_aux:
	globalInit = g[0] == 0 # global starts as 0, no process id
if pmode == mux:
	globalInit = gx[0] == 1 # global starts as 0, no process id

initList.append( globalInit ) 
if len(initList) > 1:
	init = And( initList )
else:
	init = initList[0]



# transition relation for iteration k of process i 
def stepTransition(k, i):
	ts = []
	
	if pmode == mux:
		ts.append(And( q[k][i-1] == ControlLocation.idle, q[k+1][i-1] == ControlLocation.start, identityTransition(k,i,[q],[gx]) ) )	
		ts.append(And( q[k][i-1] == ControlLocation.start, gx[k] == 1, q[k+1][i-1] == ControlLocation.cs, gx[k+1] == 0, identityTransition(k,i,[q],[]) ) )
		# buggy version: go to cs when bit is false
		#ts.append(And( q[k][i-1] == ControlLocation.start, gx[k] == 0, q[k+1][i-1] == ControlLocation.cs, gx[k+1] == 0, identityTransition(k,i,[q],[]) ) )
		ts.append(And( q[k][i-1] == ControlLocation.cs, q[k+1][i-1] == ControlLocation.idle, gx[k+1] == 1, identityTransition(k,i,[q],[]) ) )
	
	if pmode == fischer:
		# idle -> cs (buggy example)
		#ts.append(And( q[k][i-1] == ControlLocation.idle, q[k+1][i-1] == ControlLocation.cs, identityTransition(k,i,[q,x],[g]) ) )
		#ts.append(And( q[k][i-1] == ControlLocation.idle, q[k+1][i-1] == ControlLocation.cs, ForAll([j], Implies( And(j >= 1, j <= N, Distinct(i,j)), And( q[k](j) == q[k+1](j), x[k](j) == x[k+1](j), g[k] == g[k+1] ) ) ) ) )

		# idle -> start	
		ts.append(And( q[k][i-1] == ControlLocation.idle, g[k] == 0, x[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.start, identityTransition(k,i,[q,x],[g])  ) )
		#ts.append(And( q[k][i-1] == ControlLocation.idle, g[k] == 0, x[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.start, ForAll([j], Implies( And(j >= 1, j <= N, Distinct(i,j)), And( q[k](j) == q[k+1](j), x[k](j) == x[k+1](j), g[k] == g[k+1] ) ) ) ) )

		# simpler version (with cycle)
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
	
	if pmode == fischer_aux:
		# idle -> start	
		ts.append(And( q[k][i-1] == ControlLocation.idle, g[k] == 0, x[k+1][i-1] == 0, last[k+1][i-1] == x[k][i-1] + A, q[k+1][i-1] == ControlLocation.start, identityTransition(k,i,[q,x,last,first],[g])  ) )

		# start -> check
		ts.append(And( q[k][i-1] == ControlLocation.start, x[k][i-1] <= last[k][i-1], x[k+1][i-1] == 0, first[k+1][i-1] == x[k][i-1] + B, q[k+1][i-1] == ControlLocation.check, g[k+1] == i, identityTransition(k,i,[q,x,last,first],[])  ) )

		# check -> cs
		ts.append(And( q[k][i-1] == ControlLocation.check, g[k] == i, x[k][i-1] >= first[k][i-1], q[k+1][i-1] == ControlLocation.cs, identityTransition(k,i,[q,x,last,first],[g])          ) )

		# check -> idle
		ts.append(And( q[k][i-1] == ControlLocation.check, g[k] != i, x[k][i-1] >= first[k][i-1], first[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.idle, identityTransition(k,i,[q,x,last,first],[g])      ) )

		# cs -> idle
		ts.append(And( q[k][i-1] == ControlLocation.cs, q[k+1][i-1] == ControlLocation.idle, g[k+1] == 0,  identityTransition(k,i,[q,x,last,first],[])        ) )
	
	return ts

def timeTransition(k):
	# quantified indices version
	#return Exists([t1], And(t1 > 0, ForAll([j], And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], x[k+1][j-1] == x[k][j-1] + t1 )) ) ) # doesn't respect invariants
	
	ts = []
	if pmode == fischer:
		for j in range(1,Nv+1):
			# all discrete variables remain unchanged; the last implication enforces the invariant in the start location
			ts.append( And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], x[k+1][j-1] == x[k][j-1] + t1, Implies( (q[k+1][j-1] == ControlLocation.start), x[k+1][j-1] <= A ) ) )

		#p = Exists([t1], And(t1 > 0, And( ts ) ) )
		ts.append( t1 > 0 )
		p = And( ts )
		
	if pmode == fischer_aux:
		for j in range(1,Nv+1):
			# all discrete variables remain unchanged; the last implication enforces the invariant in the start location
			ts.append( And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], x[k+1][j-1] == x[k][j-1] + t1, Implies( (q[k+1][j-1] == ControlLocation.start), x[k+1][j-1] <= last[k][j-1] ) ) )
		ts.append( t1 > 0 )
		p = And( ts )
		
	if pmode == mux:
		p = False # no time transition (identity)
	print "Time transition:"
	print p
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

# return all other variables
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
	



def split_inv_tlv_ii(prop,Nv,auxc):
# prop is correctness property
# N is the number of processes in the system
#  auxc is an invariant defining auxiliary variables used in the proof
	theta = []
	for i in range(1,Nv+1):
		theta.append( [] )
		theta[i-1] = []
		for j in range(1,Nv+1):
			#theta[i-1].append( [] )
			if i != j:
				theta[i-1].append( And(initList[i-1], initList[j-1], globalInit) )
			else:
				theta[i-1].append( [] )

	print "loop until convergence. \n"
	change = 1
	index = 0

	while change:
		print "... starting iteration ", str(index), "\n"
		for i in range(1,Nv+1):
			for j in range(1,Nv+1):
				if (i != j):
					asdf = 1
					#print "theta(",str(i-1)," ",str(j-1),")"
					#print theta[i-1][j-1]

		# compute conjunction 
		print "Building conjunct"
		conj = auxc
		cList = []
		for i in range(1,Nv+1):
			for j in range(1,Nv+1):
		 		if (i != j):
					cList.append( theta[i-1][j-1] )
		conj = simplify( And(conj, And(cList) ) )
		print "Done building conjunct"
		
		gconj = Goal()
		#gconj.add( conj )
		# apply a tactic to drastically simplify conj
		#tconj = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
		#tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))
		#tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')), Repeat(Tactic('ctx-solver-simplify')))
		
		#tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')), Tactic('ctx-solver-simplify'))
		
		#tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify')), Tactic('ctx-solver-simplify'))
		#tconj = Tactic('ctx-solver-simplify')
		
		#tconj = Then( Tactic('propagate-values'), Tactic('propagate-ineqs'), Tactic('ctx-solver-simplify'))
		
		#tconj = Then( Repeat(Tactic('simplify')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat( OrElse(Tactic('split-clause'), Tactic('skip') ) ), Tactic('ctx-solver-simplify'))
		
		#tconj = Then(With('simplify', arith_lhs=True, som=True), 'normalize-bounds', 'propagate-values', 'propagate-ineqs')
		
		
		#conj = tconj( gconj ).as_expr()
		#conj = simplifyBetter( conj )
		print "Done simplifying conjunct"

		#print "conj start:"
		#print simplify(conj)
		#print "conj start end"

		# compute delta to be added to theta(i,j)
		delta = []
		for i in range(1,Nv+1):
			delta.append( [] )
			delta[i-1] = []
			for j in range(1,Nv+1):
				delta[i-1].append( False ) # start with false (identity since we're adding disjuncts)
				#print delta[i-1][j-1]
				if i != j:
				
					# only do 1 iteration, copy delta[i-1][j-1] to the others
					if not (i == 1 and j == 2):
						continue
					ts = []
					#ts.append(timeTransition(0) ) # one time transition for all k possible process moves
					
					
					#gdelta = Goal()
					#gdelta.add( delta[i-1][j-1] )
					## apply a tactic to drastically simplify delta
					#tdelta = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
					#delta[i-1][j-1] = tdelta( gdelta ).as_expr()
					#print "Done simplifying delta"
					
					bounds = []
					if pmode == mux:
						bounds = [q[0][i-1], q[0][j-1], gx[0]] # eliminate pre-state variable names
					if pmode == fischer:
						#bounds = [t1,q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], g[0]] # eliminate pre-state variable names
						bounds = [q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], g[0]] # eliminate pre-state variable names
					if pmode == fischer_aux:
						bounds = [q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], first[0][i-1], first[0][j-1], last[0][i-1], last[0][j-1], g[0]] # eliminate pre-state variable names
					bounds.extend( othersVarsPrePost_ii(i,j) ) # eliminate all other process variables (e.g., if looking at theta[0][1], eliminate vars of any process > 2)
					print "others(" + str(i) + ", " + str(j) + "):" + str(othersVarsPrePost_ii(i,j))

					
					#if pmode == fischer:
					#	tt = And(conj, timeTransition(0) )
					#	# time elapse transition
					#	tgoal = Goal()
					#	bounds.append( t1 )
					#	#tgoal.add( Exists(bounds, delta[i-1][j-1]) )
					#	tgoal.add( Exists(bounds, tt ) )
					#	ttac = Tactic('qe')
					#	print "at time transition"
					#	tr = ttac(tgoal)
					#	restime = simplify( tr.as_expr() )
					#	#delta[i-1][j-1] = Or(delta[i-1][j-1], simplify( tr.as_expr() ) )
					#	#delta[i-1][j-1] = simplify( tr.as_expr() )
					
					if pmode == fischer or pmode == fischer_aux:
						bounds.append( t1 )
						ts.append( timeTransition(0) )
					
					for k in range(1,Nv+1):
						#delta[i][j] = Or( delta[i][j], (succ(tr[k], conj) forsome others_vars[i][j]) )
						ts.extend( stepTransition(0,k) )
						
						
						
						#if pmode == mux:
						#	delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], And( conj, Or( ts ) ) ) )
						#if pmode == fischer:
						#	delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], restime, And( conj, Or( ts ) ) ) )
						delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], And( conj, Or( ts ) ) ) )
						
						##tt = And(conj, timeTransition(0) )
						## time elapse transition
						#tgoal = Goal()
						#bounds = [t1]
						#tgoal.add( Exists(bounds, delta[i-1][j-1]) )
						##tgoal.add( Exists(bounds, tt ) )
						#ttac = Tactic('qe')
						#tr = ttac(tgoal)
						##delta[i-1][j-1] = Or(delta[i-1][j-1], simplify( tr.as_expr() ) )
						#delta[i-1][j-1] = simplify( tr.as_expr() )
						
						#print "DELTA(" + str(i) + ", " + str(j) + ", " + str(k) + ")"
						#print simplify(delta[i-1][j-1])
					
					tgoal = Goal()
					#tgoal.add( And( list(s.assertions()) ) )
					# eliminate quantifiers
					
					print "simplifying goal"
					
					tgoal.add( delta[i-1][j-1] )
					
					#stac = Then(With('simplify', arith_lhs=True, som=True), 'normalize-bounds', 'propagate-values', 'propagate-ineqs')
					stac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('ctx-simplify')))

					
					
					
					rest = stac( tgoal )
					#rest = [delta[i-1][j-1]]
					
					print "before unique:"  + str(len(rest))
					
					#new_subr = []
					#for subrA in rest:
					#	for subrB in rest:
					#		if subrA == subrB:
					#			continue
					#		subr_same = Solver()
					#		subr_same.add( Not( subrA != subrB ) )
					#		if subr_same.check() == unsat: # proved unequal
					#			new_subr.append(subrA)
					#subr = new_subr	
					
					#rest = uniqueElements(rest)
					
					newList = []
					
					print "at bound elimination for iteration " + str(index)
					print bounds
					print datetime.now()
					sidx = 0
					
					scount = len(rest)
					
					for subr in rest:
						#print subr.as_expr()
						if sidx % 100 == 0:
							print "Iteration " + str(index) + ": on subterm " + str(sidx) + " of " + str(scount)
						sidx = sidx + 1
					
						tgoal = Goal()
						
						#print subr.as_expr()
						
						
						tgoal.add( Exists(bounds, subr.as_expr() ) )
						#tgoal.add( Exists(bounds, subr) )
						
						
						
						#tgoal.add( delta[i-1][j-1])
						#ttac = Then(Repeat(Tactic('split-clause')), Tactic('qe'))
						#ttac = Tactic('elim-uncnstr')
						#ttac = Tactic('snf')
						ttac = Tactic('qe')

						#print tgoal
						
						tr = ttac(tgoal)
						#newstates = simplify(tr.as_expr()) 
						newList.append( simplify(tr.as_expr() ) )

						#for vn in bounds:
						#	print vn
						#	rep = vn == ControlLocation.cs
						#	print rep
						#	delta[i-1][j-1] = substitute( delta[i-1][j-1], (vn,rep) )

						#newstates = delta[i-1][j-1]
					newstates = Or(newList)


					# rename post-state to pre-state (x' -> x)
					delta[i-1][j-1] = newstates
					kfrom = 1
					kto = 0
					for idx in range(1,Nv+1):
						if pmode == fischer:
							delta[i-1][j-1] = simplify( substitute( delta[i-1][j-1], (q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (g[kfrom],g[kto]) ) )
						if pmode == fischer_aux:
							delta[i-1][j-1] = simplify( substitute( delta[i-1][j-1], (q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (g[kfrom],g[kto]), (first[kfrom][idx-1],first[kto][idx-1]), (last[kfrom][idx-1],last[kto][idx-1]) ) )
						if pmode == mux:
							delta[i-1][j-1] = simplify( substitute( delta[i-1][j-1], (q[kfrom][idx-1],q[kto][idx-1]), (gx[kfrom],gx[kto]) ) )
							
					#gnew = Goal()
					#gnew.add( delta[i-1][j-1] )
					## apply a tactic to drastically simplify conj
					#tnew = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
					#delta[i-1][j-1] = tnew( gnew ).as_expr()
					#print "Done simplifying new states"
					print "TRANSITION(" + str(i) + ", " + str(j) + ")"
					#print delta[i-1][j-1]
					#break
			#break
		#break

		# add new states
		newtheta = []
		for i in range(1,Nv+1):
			newtheta.append( [] )
			newtheta[i-1] = []
			for j in range(1,Nv+1):
				newtheta[i-1].append( [] )
				if i != j:
					#print "updating theta"
					if not (i == 1 and j == 2):
						kfrom = 0
						kto = 0
						ifrom = 1
						ito = i
						jfrom = 2
						jto = j
						delta[i-1][j-1] = substitute( delta[ifrom-1][jfrom-1], (q[kfrom][ifrom-1],q[kto][ito-1]), (q[kfrom][jfrom-1],q[kto][jto-1]) )
					
					newtheta[i-1][j-1] = simplify( Or(theta[i-1][j-1], delta[i-1][j-1]) )
					#print newtheta[i-1][j-1]

		# check for change
		change = False
		for i in range(1,Nv+1):
			for j in range(1,Nv+1):
				if i != j:
					#print "changing"
					# unprime vars
					#kfrom = 1
					#kto = 0
					#for idx in range(1,Nv+1):
						#newtheta[i-1][j-1] = substitute(newtheta[i-1][j-1], (q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (g[kfrom],g[kto]) )
					#	newtheta[i-1][j-1] = substitute(newtheta[i-1][j-1], (q[kfrom][idx-1],q[kto][idx-1]), (gx[kfrom],gx[kto]) )
					#print (theta[i-1][j-1] == newtheta[i-1][j-1])
					
					s.push()
					s.add( Not(theta[i-1][j-1] == newtheta[i-1][j-1]) )
					res = s.check()
					unequal = True
					if res == unsat: # proved 2 expressions are equal
						unequal = False
					s.pop()
					change = change or unequal
					#print change
					
					theta[i-1][j-1] = newtheta[i-1][j-1]
				
					#print theta[i-1][j-1]
					
		#break


		
		if index >= 50:
			print "Quit by bound after " + str(index) + " iterations."
			break
		
		if change:
			# increment counter
			index = index + 1

	
	print "finished split invariant computation after " + str(index) + " iterations. \n"

	print "Potential invariant:"
	#for i in range(1,Nv+1):
	#	for j in range(1,Nv+1):
	#		print "Inv(" + str(i) + ", " + str(j) + "):"
	#		print theta[i-1][j-1]
	print theta[0][1]
	
	print "finished split invariant computation after " + str(index) + " iterations. \n"
	
	print "\nchecking for violations\n";

	# step 4: check for violation 
	# i.e., check if [(/\i,j: i \neq j: theta(i,j)) & auxc -> prop]
	# i.e., check if (/\i,j: i \neq j: theta(i,j)) & auxc & not(prop) is satisfiable

	#viol = And(auxc, Not(prop) )
	#print viol

	qf = Function('qf', IntSort(), ControlLocation)	
	if pmode == mux:
		gxf = Int('gxf')
	if pmode == fischer or pmode == fischer_aux:
		xf = Function('xf', IntSort(), RealSort())
		gf = Int('gf')
	if pmode == fischer_aux:
		lastf = Function('lastf', IntSort(), RealSort())
		firstf = Function('firstf', IntSort(), RealSort())
	
	
	#for i in range(1,Nv+1):
	#	for i in range(1,Nv+1):
	#		if (i != j):
				#viol = And(viol, theta[i-1][j-1])
	i = 1
	j = 2
	
	
	if pmode == fischer:
		xgoal = Goal()
		#xgoal.add( delta[i-1][j-1])
		#xtac = Tactic('qe')
		#delta[i-1][j-1] = xtac( Exists([x[0][0], x[0][1]], delta[i-1][j-1] ) ).as_expr()
	
	kfrom = 0
	iidx = Int('i')
	jidx = Int('j')
	
		
	if pmode == mux:
		quant = simplify( substitute(delta[i-1][j-1], (q[kfrom][i-1], qf(iidx) ), (q[kfrom][j-1], qf(jidx) ), (gx[kfrom],gxf ) ) )
	if pmode == fischer:
		quant = simplify( substitute(delta[i-1][j-1], (q[kfrom][i-1], qf(iidx) ), (q[kfrom][j-1], qf(jidx) ), (x[kfrom][i-1], xf(iidx) ), (x[kfrom][j-1], xf(jidx) ), (g[kfrom],gf ) ) )
	if pmode == fischer_aux:
		quant = simplify( substitute(delta[i-1][j-1], (q[kfrom][i-1], qf(iidx) ), (q[kfrom][j-1], qf(jidx) ), (x[kfrom][i-1], xf(iidx) ), (x[kfrom][j-1], xf(jidx) ), (g[kfrom],gf ), (last[kfrom][i-1], lastf(iidx) ), (last[kfrom][j-1], lastf(jidx) ), (first[kfrom][i-1], firstf(iidx) ), (first[kfrom][j-1], firstf(jidx) ) ) )
	print quant
	
	
	quant = ForAll([iidx, jidx], Implies(indexBounds_ii(iidx,jidx), quant))
	
	
	
	viol = And(quant, Not(safetyQ(iidx, jidx, qf) ))

	s.push()
	s.add(viol)
	res = s.check()
	s.pop()
	
	#print viol
	print res
	
	print Not(safetyQ(iidx, jidx, qf) )
	
	if res == sat:
		print "!!!!! violation !!!!!\n"
		print viol
		print "a satisfying assignment\n"
		print s.model()
	else:
		print "No violation found\n"

	
	print "quantified invariant:"

	#qtac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
	#qgoal = Goal()
	#qgoal.add( quant )
	#rq = qtac( quant ).as_expr()
	#rq = toCnf(rq)
	print quant

	fptr = open("quant-ii-" + str(pmode) + ".smt", 'w')
	fptr.write( quant.sexpr().replace("qf","q").replace("gxf","x").replace("xf","x").replace("gf","g").replace("<","&lt;").replace(">","&gt;").replace("= g 1","= g i").replace("= g 2","= g j").replace("(= g 3)", "(not (= g i)) (not (= g j))").replace("(= g 0)", "(not (= g i)) (not (= g j))").replace("lastf","last").replace("firstf","first") )
	fptr.close()

































def split_inv_tlv_i(prop,Nv,auxc):
# prop is correctness property
# N is the number of processes in the system
#  auxc is an invariant defining auxiliary variables used in the proof
	theta = []
	for i in range(1,Nv+1):
		theta.append( [] )
		theta[i-1] = And(initList[i-1], globalInit)

	print "loop until convergence. \n"
	change = 1
	index = 0

	while change:
		print "... starting iteration ", str(index), "\n"

		# compute conjunction 
		print "Building conjunct"
		conj = auxc
		cList = []
		for i in range(1,Nv+1):
			cList.append( theta[i-1] )
		print conj
		print cList
		conj = simplify( And(conj, And(cList) ) )
		print "Done building conjunct"
		
		gconj = Goal()
		gconj.add( conj )
		# apply a tactic to drastically simplify conj
		#tconj = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
		#tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))
		tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))
		conj = tconj( gconj ).as_expr()
		print "Done simplifying conjunct"

		#print "conj start:"
		#print simplify(conj)
		#print "conj start end"

		# compute delta to be added to theta(i,j)
		delta = []
		for i in range(1,Nv+1):
			delta.append( [] )
			delta[i-1] = False # start with false (identity since we're adding disjuncts)
			#print delta[i-1][j-1]

			# only do 1 iteration, copy delta[i-1][j-1] to the others
			if not (i == 1):
				continue
			ts = []
			#ts.append(timeTransition(0) ) # one time transition for all k possible process moves


			#gdelta = Goal()
			#gdelta.add( delta[i-1][j-1] )
			## apply a tactic to drastically simplify delta
			#tdelta = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
			#delta[i-1][j-1] = tdelta( gdelta ).as_expr()
			#print "Done simplifying delta"

			bounds = []
			if pmode == mux:
				bounds = [q[0][i-1], gx[0]] # eliminate pre-state variable names
			if pmode == fischer:
				#bounds = [t1,q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], g[0]] # eliminate pre-state variable names
				bounds = [q[0][i-1], x[0][i-1], g[0]] # eliminate pre-state variable names
			if pmode == fischer_aux:
				#bounds = [t1,q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], g[0]] # eliminate pre-state variable names
				bounds = [q[0][i-1], x[0][i-1], first[0][i-1], last[0][i-1], g[0]] # eliminate pre-state variable names
			bounds.extend( othersVarsPrePost_i(i) ) # eliminate all other process variables (e.g., if looking at theta[0][1], eliminate vars of any process > 2)
			print "others(" + str(i) + "):" + str(othersVarsPrePost_i(i))


			#if pmode == fischer:
			#	tt = And(conj, timeTransition(0) )
			#	# time elapse transition
			#	tgoal = Goal()
			#	bounds.append( t1 )
			#	#tgoal.add( Exists(bounds, delta[i-1][j-1]) )
			#	tgoal.add( Exists(bounds, tt ) )
			#	ttac = Tactic('qe')
			#	print "at time transition"
			#	tr = ttac(tgoal)
			#	restime = simplify( tr.as_expr() )
			#	#delta[i-1][j-1] = Or(delta[i-1][j-1], simplify( tr.as_expr() ) )
			#	#delta[i-1][j-1] = simplify( tr.as_expr() )

			if pmode == fischer or pmode == fischer_aux:
				bounds.append( t1 )
				ts.append( timeTransition(0) )

			for k in range(1,Nv+1):
				#delta[i][j] = Or( delta[i][j], (succ(tr[k], conj) forsome others_vars[i][j]) )
				ts.extend( stepTransition(0,k) )



				#if pmode == mux:
				#	delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], And( conj, Or( ts ) ) ) )
				#if pmode == fischer:
				#	delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], restime, And( conj, Or( ts ) ) ) )
				delta[i-1] = simplify( Or( delta[i-1], And( conj, Or( ts ) ) ) )

				##tt = And(conj, timeTransition(0) )
				## time elapse transition
				#tgoal = Goal()
				#bounds = [t1]
				#tgoal.add( Exists(bounds, delta[i-1][j-1]) )
				##tgoal.add( Exists(bounds, tt ) )
				#ttac = Tactic('qe')
				#tr = ttac(tgoal)
				##delta[i-1][j-1] = Or(delta[i-1][j-1], simplify( tr.as_expr() ) )
				#delta[i-1][j-1] = simplify( tr.as_expr() )

				#print "DELTA(" + str(i) + ", " + str(j) + ", " + str(k) + ")"
				#print simplify(delta[i-1][j-1])

			tgoal = Goal()
			# eliminate quantifiers

			print "simplifying goal"

			tgoal.add( delta[i-1] )
			
			stac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('ctx-solver-simplify')))
			
			#stac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))
			
			#stac = Repeat(Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify'))))
			#stac = Repeat(Then( Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify'))))


			#stac = Then( Tactic('propagate-values'), Tactic('propagate-ineqs'))

			#stac = Tactic('split-clause')
			rest = stac( tgoal )
			#rest = [delta[i-1][j-1]]

			print "before unique:"  + str(len(rest))

			#new_subr = []
			#for subrA in rest:
			#	for subrB in rest:
			#		if subrA == subrB:
			#			continue
			#		subr_same = Solver()
			#		subr_same.add( Not( subrA != subrB ) )
			#		if subr_same.check() == unsat: # proved unequal
			#			new_subr.append(subrA)
			#subr = new_subr	

			#rest = uniqueElements(rest)

			newList = []

			print "at bound elimination for iteration " + str(index)
			print bounds
			print datetime.now()
			sidx = 0

			scount = len(rest)

			for subr in rest:
				#print subr.as_expr()
				if sidx % 100 == 0:
					print "Iteration " + str(index) + ": on subterm " + str(sidx) + " of " + str(scount)
				sidx = sidx + 1

				tgoal = Goal()

				#print subr.as_expr()


				tgoal.add( Exists(bounds, subr.as_expr() ) )
				#tgoal.add( Exists(bounds, subr) )



				#tgoal.add( delta[i-1][j-1])
				#ttac = Then(Repeat(Tactic('split-clause')), Tactic('qe'))
				#ttac = Tactic('elim-uncnstr')
				#ttac = Tactic('snf')
				ttac = Tactic('qe')

				#print tgoal

				tr = ttac(tgoal)
				#newstates = simplify(tr.as_expr()) 
				newList.append( simplify(tr.as_expr() ) )

				#for vn in bounds:
				#	print vn
				#	rep = vn == ControlLocation.cs
				#	print rep
				#	delta[i-1][j-1] = substitute( delta[i-1][j-1], (vn,rep) )

				#newstates = delta[i-1][j-1]
			newstates = Or(newList)


			# rename post-state to pre-state (x' -> x)
			delta[i-1] = newstates
			kfrom = 1
			kto = 0
			for idx in range(1,Nv+1):
				if pmode == fischer:
					delta[i-1] = simplify( substitute( delta[i-1], (q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (g[kfrom],g[kto]) ) )
				if pmode == fischer_aux:
					delta[i-1] = simplify( substitute( delta[i-1], (q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (last[kfrom][idx-1],last[kto][idx-1]), (first[kfrom][idx-1],first[kto][idx-1]), (g[kfrom],g[kto]) ) )
				if pmode == mux:
					delta[i-1] = simplify( substitute( delta[i-1], (q[kfrom][idx-1],q[kto][idx-1]), (gx[kfrom],gx[kto]) ) )

			#gnew = Goal()
			#gnew.add( delta[i-1][j-1] )
			## apply a tactic to drastically simplify conj
			#tnew = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
			#delta[i-1][j-1] = tnew( gnew ).as_expr()
			#print "Done simplifying new states"
			print "TRANSITION(" + str(i) + ")"
			#print delta[i-1][j-1]
			#break
		#break
	#break

		# add new states
		newtheta = []
		for i in range(1,Nv+1):
			newtheta.append( [] )
			newtheta[i-1] = []
			newtheta[i-1].append( [] )
			#print "updating theta"
			if not (i == 1):
				kfrom = 0
				kto = 0
				ifrom = 1
				ito = i
				if pmode == mux:
					delta[i-1] = substitute( delta[ifrom-1], (q[kfrom][ifrom-1],q[kto][ito-1])  )
				if pmode == fischer:
					delta[i-1] = substitute( delta[ifrom-1], (q[kfrom][ifrom-1],q[kto][ito-1]), (x[kfrom][ifrom-1],x[kto][ito-1])  )
				if pmode == fischer_aux:
					delta[i-1] = substitute( delta[ifrom-1], (q[kfrom][ifrom-1],q[kto][ito-1]), (x[kfrom][ifrom-1],x[kto][ito-1]), (last[kfrom][ifrom-1],last[kto][ito-1]), (first[kfrom][ifrom-1],first[kto][ito-1])  )

			newtheta[i-1] = simplify( Or(theta[i-1], delta[i-1]) )
			#print newtheta[i-1][j-1]

		# check for change
		change = False
		for i in range(1,Nv+1):
			#print "changing"
			# unprime vars
			#kfrom = 1
			#kto = 0
			#for idx in range(1,Nv+1):
				#newtheta[i-1][j-1] = substitute(newtheta[i-1][j-1], (q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (g[kfrom],g[kto]) )
			#	newtheta[i-1][j-1] = substitute(newtheta[i-1][j-1], (q[kfrom][idx-1],q[kto][idx-1]), (gx[kfrom],gx[kto]) )
			#print (theta[i-1][j-1] == newtheta[i-1][j-1])

			s.push()
			s.add( Not(theta[i-1] == newtheta[i-1]) )
			res = s.check()
			unequal = True
			if res == unsat: # proved 2 expressions are equal
				unequal = False
			s.pop()
			change = change or unequal
			#print change

			theta[i-1] = newtheta[i-1]
			
		if index >= 50:
			print "Quit by bound after " + str(index) + " iterations."
			break
		
		if change:
			# increment counter
			index = index + 1

	
	print "finished split invariant computation after " + str(index) + " iterations. \n"

	print "Potential invariant:"
	#for i in range(1,Nv+1):
	#	for j in range(1,Nv+1):
	#		print "Inv(" + str(i) + ", " + str(j) + "):"
	#		print theta[i-1][j-1]
	print theta[0]
	
	print "finished split invariant computation after " + str(index) + " iterations. \n"
	
	print "\nchecking for violations\n";

	# step 4: check for violation 
	# i.e., check if [(/\i,j: i \neq j: theta(i,j)) & auxc -> prop]
	# i.e., check if (/\i,j: i \neq j: theta(i,j)) & auxc & not(prop) is satisfiable

	#viol = And(auxc, Not(prop) )
	#print viol

	qf = Function('qf', IntSort(), ControlLocation)	
	if pmode == mux:
		gxf = Int('gxf')
	if pmode == fischer or pmode == fischer_aux:
		xf = Function('xf', IntSort(), RealSort())
		gf = Int('gf')
	if pmode == fischer_aux:
		lastf = Function('lastf', IntSort(), RealSort())
		firstf = Function('firstf', IntSort(), RealSort())
	
	
	#for i in range(1,Nv+1):
	#	for i in range(1,Nv+1):
	#		if (i != j):
				#viol = And(viol, theta[i-1][j-1])
	i = 1
	
	
	if pmode == fischer:
		xgoal = Goal()
		#xgoal.add( delta[i-1][j-1])
		#xtac = Tactic('qe')
		#delta[i-1][j-1] = xtac( Exists([x[0][0], x[0][1]], delta[i-1][j-1] ) ).as_expr()
	
	kfrom = 0
	iidx = Int('i')
	jidx = Int('j')
	
		
	if pmode == mux:
		quant = simplify( substitute(delta[i-1], (q[kfrom][i-1], qf(iidx) ), (gx[kfrom],gxf ) ) )
	if pmode == fischer:
		quant = simplify( substitute(delta[i-1], (q[kfrom][i-1], qf(iidx) ), (x[kfrom][i-1], xf(iidx) ), (g[kfrom],gf ) ) )
	if pmode == fischer_aux:
		quant = simplify( substitute(delta[i-1], (q[kfrom][i-1], qf(iidx) ), (x[kfrom][i-1], xf(iidx) ), (g[kfrom],gf ), (last[kfrom][i-1], lastf(iidx) ), (first[kfrom][i-1], firstf(iidx) ) ) )
	print quant
	
	
	quant = ForAll([iidx], Implies(indexBounds_i(iidx), quant))
	
	
	
	viol = And(quant, Not(safetyQ(iidx, jidx, qf) ))

	s.push()
	s.add(viol)
	res = s.check()
	s.pop()
	
	#print viol
	print res
	
	print Not(safetyQ(iidx, jidx, qf) )
	
	if res == sat:
		print "!!!!! violation !!!!!\n"
		print viol
		print "a satisfying assignment\n"
		print s.model()
	else:
		print "No violation found\n"

	
	print "quantified invariant:"

	#qtac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
	#qgoal = Goal()
	#qgoal.add( quant )
	#rq = qtac( quant ).as_expr()
	#rq = toCnf(rq)
	print quant

	fptr = open("quant-i-" + str(pmode) + ".smt", 'w')
	fptr.write( quant.sexpr().replace("qf","q").replace("gxf","x").replace("xf","x").replace("gf","g").replace("<","&lt;").replace(">","&gt;").replace("= g 1","= g i").replace("(= g 2)","(not (= g i))").replace("(= g 3)", "(not (= g i))").replace("(= g 0)", "(not (= g i))") )
	fptr.close()





































def safetyQ(i,j,q):
	return ForAll([i,j], Implies( indexBounds_ii(i,j), Or( q(i) != ControlLocation.cs, q(j) != ControlLocation.cs) ))

def safety(Nv):
	sList = []
	for i in range(1,Nv+1):
		nList = []
		for j in range(1,Nv+1):
			if i == j:
				continue
			#sList.append( Implies( q[0][i-1] == ControlLocation.cs, q[0][j-1] != ControlLocation.cs ) )
			#sList.append( Or(q[0][i-1] != ControlLocation.cs, q[0][j-1] != ControlLocation.cs ) )
			nList.append( q[0][j-1] != ControlLocation.cs )
		sList.append( Implies(q[0][i-1] == ControlLocation.cs, And(nList) ) )
	return And( sList )


def indexBounds_ii(i,j):
	return And( 1 <= i, i <= N, 1 <= j, j <= N, i != j)
	

def indexBounds_i(i):
	return And( 1 <= i, i <= N)



def othersVars(m,n):
	ov = []
	for i in range(1,Nv+1):	
		if i != m and i != n:
			if pmode == fischer or pmode == fischer_aux:
				ov.extend( [q[0][i-1], x[0][i-1]] )
			if pmode == fischer_aux:
				ov.extend( [last[0][i-1], first[0][i-1]] )
			if pmode == mux:
				ov.extend( [q[0][i-1]] )
	return ov
	

def othersVars(m):
	ov = []
	for i in range(1,Nv+1):	
		if i != m:
			if pmode == fischer or pmode == fischer_aux:
				ov.extend( [q[0][i-1], x[0][i-1]] )
			if pmode == fischer_aux:
				ov.extend( [first[0][i-1], last[0][i-1]] )
			if pmode == mux:
				ov.extend( [q[0][i-1]] )
	return ov
	

def uniqueElements(seq):
   # Not order preserving    
   set = Set(seq)
   return list(set)
  

def othersVarsPrePost_ii(m,n):
	ov = []
	for i in range(1,Nv+1):	
		if i != m and i != n:
			if pmode == fischer or pmode == fischer_aux:
				ov.extend( [q[0][i-1], x[0][i-1]] )
				ov.extend( [q[1][i-1], x[1][i-1]] )
			if pmode == fischer_aux:
				ov.extend( [first[0][i-1], last[0][i-1]] )
				ov.extend( [first[1][i-1], last[1][i-1]] )
			if pmode == mux:
				ov.extend( [q[0][i-1]] )
				ov.extend( [q[1][i-1]] )
	return ov
	
def othersVarsPrePost_i(m):
	ov = []
	for i in range(1,Nv+1):	
		if i != m:
			if pmode == fischer or pmode == fischer_aux:
				ov.extend( [q[0][i-1], x[0][i-1]] )
				ov.extend( [q[1][i-1], x[1][i-1]] )
			if pmode == fischer_aux:
				ov.extend( [first[0][i-1], last[0][i-1]] )
				ov.extend( [first[1][i-1], last[1][i-1]] )
			if pmode == mux:
				ov.extend( [q[0][i-1]] )
				ov.extend( [q[1][i-1]] )
	return ov

def simplifyBetter(expr):
	g = Goal()
	g.add( expr )
	#tac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('ctx-solver-simplify')))
	
	tac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')))
	
	#stac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))

	#stac = Repeat(Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify'))))
	#stac = Repeat(Then( Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify'))))


	#stac = Then( Tactic('propagate-values'), Tactic('propagate-ineqs'))

	#stac = Tactic('split-clause')
	
	#stac = Repeat(Then(Tactic('split-clause'), Tactic('elim-and')))
	#stac = Then(Tactic('split-clause'),Tactic('elim-and'),Tactic('nnf'))
	#stac = Repeat( OrElse( Tactic('split-clause'), Tactic('elim-and') ) )
	#stac = Repeat( OrElse( Then(Tactic('split-clause'),Tactic('elim-and'),Tactic('nnf')), Tactic('skip') ) )
	#stac = Repeat( OrElse( Then(Tactic('split-clause'),Tactic('elim-and'),Tactic('nnf')), Tactic('skip') ) )

	# split all clauses
	#stac = Repeat(OrElse(Tactic('split-clause'), Tactic('skip')))

	#stac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('nnf')))
	#
	#stac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('elim-uncnstr')))

	# lower
	#stac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')) )

	# lowest now
	#stac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')))

	#
	#stac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('aig')), Repeat(Tactic('simplify')))

	#stac = Repeat(Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify'))))

	#stac = Repeat(Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify'))))

	#stac = Then(Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and'))), Repeat(Tactic('propagate-values')), ParThen(Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify'))))



	#stac = OrElse(TryFor(Repeat(Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))), 10*1000), Tactic('skip'))





	#stac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))


	#stac = Then( OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
	#stac = Repeat(Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')), Repeat(Tactic('ctx-solver-simplify'))))

	#stac = Repeat(Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify')), Repeat(Tactic('ctx-solver-simplify'))))

	#stac = Then( Repeat(Tactic('simplify')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat( OrElse(Tactic('split-clause'), Tactic('skip') ) ), Tactic('ctx-solver-simplify'))
	#stac = Then( Tactic('propagate-values'), Tactic('propagate-ineqs'))

	#stac = Tactic('split-clause')
	
	
	return tac( g ).as_expr()
	

def toCnf(expr):
	g1 = Goal()
	g1.add( expr )
	#'(then (! simplify :elim-and true) elim-term-ite tseitin-cnf)'
	tac1 = Then( With(Tactic('simplify'), elim_and=True), Tactic('elim-term-ite'), With(Tactic('tseitin-cnf'), distributivity=False))
	rcnf = tac1( g1 )
	return rcnf.as_expr()



#split_inv_tlv_i(safety(Nv),Nv,True)


split_inv_tlv_ii(safety(Nv),Nv,True)