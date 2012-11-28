import sys

#sys.path.append("D:\Dropbox\Research\tools\z3\z3-latest\bin")
#init("z3.dll")
from z3 import *
from sets import Set
import time
from datetime import *

# control locations defined as an enumeration datatype
ControlLocation = Datatype('Location')

fischer = 0
mux = 1
fischer_aux = 2
sats_3loc = 3
pmode = fischer

ctx = main_ctx()
ctx.set(PP_MIN_ALIAS_SIZE=1000)
ctx.set(PULL_NESTED_QUANTIFIERS=True)

set_option(max_depth=1000)
set_option(max_lines=1000)
set_option(PP_MIN_ALIAS_SIZE=1000) # doesn't work, at least not for .sexpr()

if pmode == fischer or pmode == fischer_aux or pmode == mux:
	ControlLocation.declare('idle')
	ControlLocation.declare('start')
	if pmode == fischer or pmode == fischer_aux:
		ControlLocation.declare('check')
	ControlLocation.declare('cs')
if pmode == sats_3loc:
	ControlLocation.declare('fly')
	ControlLocation.declare('base')
	ControlLocation.declare('landed')
ControlLocation = ControlLocation.create()

s = Solver() # instantiate a solver


q=[] # list of steps for control location

lvars = []
gvars = []

if pmode == sats_3loc:
	x=[]
	#barray=[]
if pmode == fischer or pmode == fischer_aux:
	x=[] # list of steps for continuous variable x
	g=[] # list of steps for global variable g
	lvars.append( x )
	gvars.append( g )
if pmode == fischer_aux:
	last=[]
	first=[]
	lvars.append( last )
	lvars.append( first )
if pmode == mux:
	gx=[]
	gvars.append( gx )

r = Int("r")
i, j, N = Ints("i j N")

assump = []

if pmode == mux or pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
	t1 = Real("t1") # time elapse variable
	t2 = Real("t2") # time elapse variable
	delta = Real("delta") # time elapse variable
	if pmode == fischer or pmode == fischer_aux:
		#A, B, c, d = Reals("A B c d")
		#assump.append(A == 1) # safe if A < B; buggy (multiple processes in critical section) if A >= B
		#assump.append(B == 10)
		#assump.append(And(A > 0, B > 0))
		#assump.append(A < B) # you don't have to pick actual values for A or B
		#assump.append(A == 5)
		#assump.append(B == 7)
		A = 5
		B = 7
	if pmode == sats_3loc:
		#a, b, LB, LS, LGUARD = Reals("a b LB LS LGUARD")
		#assump.append(a == 90)
		#assump.append(b == 120)
		#assump.append(LB == 5 + 10 + 13)
		#assump.append(LS == 7)
		#assump.append(LGUARD == LS + (b - a) * ((LB - LS) / a))
		
		# define as actual values, otherwise we have to do a nonlinear q.e. (or we won't be able to eliminate all the quantifiers)
		a = 90
		b = 120
		LB = 5 + 10 + 13
		LS = 7
		LGUARD = LS + (b - a) * ((LB - LS) / a)

Nv = 3 # number of processes
Pv = 2

assump.append(N == Nv) # TODO: >= ?

# allocate 1st vars
for k in range(2):
	if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
		x.append( [] )
	if pmode == fischer_aux:
		last.append( [] )
		first.append( [] )
	#if pmode == sats_3loc:
	#	barray.append( [] )
	q.append( [] )
	for i in range(1,Nv+1):		
		q[k].append( Const( 'q' + str(i) + "_" + str(k), ControlLocation) )
		if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
			x[k].append( Real('x' + str(i) + "_" + str(k)) )			
			assump.append( x[k][i-1] >= 0 ) # all processes have nonnegative clocks at all steps
		#if pmode == sats_3loc:
			#barray[k].append( Int('b' + str(i) + "_" + str(k)) )
			#assump.append( And(barray[k][i-1] >= 0, barray[k][i-1] <= 1) )
		if pmode == fischer_aux:
			last[k].append( Real('last' + str(i) + "_" + str(k)) )
			first[k].append( Real('first' + str(i) + "_" + str(k)) )
			assump.append( last[k][i-1] >= 0 ) # all processes have nonnegative clocks at all steps
			assump.append( first[k][i-1] >= 0 ) # all processes have nonnegative clocks at all steps
	if pmode == fischer or pmode == fischer_aux:
		g.append( Int("g" + str(k)) )
		assump.append(And( g[k] >= 0, g[k] <= Nv) ) # global variable is either a process id 1, ... N, or none of them (0)
	if pmode == mux:
		gx.append( Int("gx" + str(k)) )
		assump.append(And( gx[k] >= 0, gx[k] <= 1) ) # global variable is a bit
	#if pmode == fischer_aux:
	#	for i in range(1,Nv+1):
	#		for j in range(1,Nv+1):
	#			if i != j:
	#				assump.append( x[k][i-1] == x[k][j-1] ) # all processes have equal clocks at all steps
s.add( And( assump ) )
print "Assumptions: "
print assump


initList = []
# generate initial condition over all processes
for m in range(1,Nv+1):
	initList.append([])
	if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
		initList[m-1].append( x[0][m-1] == 0 )
	#if pmode == sats_3loc:
		#initList.append( barray[0][m-1] == 0 )
	if pmode == fischer_aux:
		initList[m-1].append( last[0][m-1] == A )
		initList[m-1].append( first[0][m-1] == 0 )
	if pmode == fischer or pmode == fischer_aux or pmode == mux:
		initList[m-1].append( q[0][m-1] == ControlLocation.idle )
	if pmode == sats_3loc:
		initList[m-1].append( q[0][m-1] == ControlLocation.fly )

if pmode == fischer or pmode == fischer_aux:
	globalInit = g[0] == 0 # global starts as 0, no process id
if pmode == mux:
	globalInit = gx[0] == 1 # global starts as 0, no process id



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
		ts.append(And( q[k][i-1] == ControlLocation.idle, g[k] == 0, last[k+1][i-1] == x[k][i-1] + A, q[k+1][i-1] == ControlLocation.start, identityTransition(k,i,[q,x,last,first],[g])  ) )

		# start -> check
		ts.append(And( q[k][i-1] == ControlLocation.start, x[k][i-1] <= last[k][i-1], first[k+1][i-1] == x[k][i-1] + B, q[k+1][i-1] == ControlLocation.check, g[k+1] == i, identityTransition(k,i,[q,x,last,first],[])  ) )

		# check -> cs
		ts.append(And( q[k][i-1] == ControlLocation.check, g[k] == i, x[k][i-1] >= first[k][i-1], q[k+1][i-1] == ControlLocation.cs, identityTransition(k,i,[q,x,last,first],[g])          ) )

		# check -> idle
		ts.append(And( q[k][i-1] == ControlLocation.check, g[k] != i, x[k][i-1] >= first[k][i-1], first[k+1][i-1] == 0, q[k+1][i-1] == ControlLocation.idle, identityTransition(k,i,[q,x,last,first],[g])      ) )

		# cs -> idle
		ts.append(And( q[k][i-1] == ControlLocation.cs, q[k+1][i-1] == ControlLocation.idle, g[k+1] == 0,  identityTransition(k,i,[q,x,last,first],[])        ) )
		

	if pmode == sats_3loc:
		j = 2
		ug = universalGuard(Implies((q[k][j-1] == ControlLocation.base),  (x[k][j-1] >= LGUARD)),i,j,k)
		#ug = universalGuard(Implies((barray[k][j-1] == 1),  (x[k][j-1] >= LGUARD)),i,j,k)
		#ts.append(And( q[k][i-1] == ControlLocation.fly, q[k+1][i-1] == ControlLocation.base, barray[k+1][i-1] == 1, ug, identityTransition(k,i,[x,q],[]) ) )
		#ts.append(And( q[k][i-1] == ControlLocation.base, q[k+1][i-1] == ControlLocation.fly, x[k+1][i-1] == 0, barray[k+1][i-1] == 0, identityTransition(k,i,[q],[]) ) )
		#ts.append(And( q[k][i-1] == ControlLocation.base, q[k+1][i-1] == ControlLocation.landed, x[k+1][i-1] == 0, barray[k+1][i-1] == 0, identityTransition(k,i,[q],[]) ) )
		
		ts.append(And( q[k][i-1] == ControlLocation.fly, q[k+1][i-1] == ControlLocation.base, ug, identityTransition(k,i,[x,q],[]) ) )
		ts.append(And( q[k][i-1] == ControlLocation.base, q[k+1][i-1] == ControlLocation.fly, x[k+1][i-1] == 0, identityTransition(k,i,[q],[]) ) )
		ts.append(And( q[k][i-1] == ControlLocation.base, q[k+1][i-1] == ControlLocation.landed, x[k+1][i-1] == 0, identityTransition(k,i,[q],[]) ) )
		
		#ts.append(And( q[k][i-1] == ControlLocation.fly, q[k+1][i-1] == ControlLocation.base, identityTransition(k,i,[x,q],[]) ) )
		#ts.append(And( q[k][i-1] == ControlLocation.base, q[k+1][i-1] == ControlLocation.fly, identityTransition(k,i,[x,q],[]) ) )
		#ts.append(And( q[k][i-1] == ControlLocation.base, q[k+1][i-1] == ControlLocation.landed, identityTransition(k,i,[x,q],[]) ) )
	
	for v in range(len(ts)):
		ts[v] = simplifyBetterConj( ts[v] ).as_expr()
		
		
	return ts

def timeTransition(k):
	# quantified indices version
	#return Exists([t1], And(t1 > 0, ForAll([j], And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], x[k+1][j-1] == x[k][j-1] + t1 )) ) ) # doesn't respect invariants
	
	ts = []
	if pmode == fischer:
		for j in range(1,Nv+1):
			# all discrete variables remain unchanged; the last implication enforces the invariant in the start location
			#ts.append( And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], x[k+1][j-1] == x[k][j-1] + t1, Implies( (q[k][j-1] == ControlLocation.start), x[k+1][j-1] <= A ) ) )
			#ts.append( And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], x[k+1][j-1] == x[k][j-1] + t1 ) )
			
			ts.append( And( q[k+1][j-1] == q[k][j-1], g[k+1] == g[k], And(
				Implies( (q[k][j-1] == ControlLocation.idle), x[k+1][j-1] == x[k][j-1] ),
				Implies( (q[k][j-1] == ControlLocation.start), And(x[k+1][j-1] == x[k][j-1] + t1, x[k][j-1] + t1 <= A ) ),
				Implies( (q[k][j-1] == ControlLocation.check), And(x[k+1][j-1] == x[k][j-1] + t1, x[k][j-1] + t1 <= 2*B ) ),
				Implies( (q[k][j-1] == ControlLocation.cs), x[k+1][j-1] == x[k][j-1] ) ) ) )

		ts.append( t1 > 0 )
		p = And( ts )
		#p = Exists([t1], p )
		
		
		
	if pmode == fischer_aux:
		for j in range(1,Nv+1):
			# all discrete variables remain unchanged; the last implication enforces the invariant in the start location
			#ts.append( And( q[k+1][j-1] == q[k][j-1], first[k+1][j-1] == first[k][j-1], last[k+1][j-1] == last[k][j-1], Implies( (q[k][j-1] == ControlLocation.start), And(x[k][j-1] <= last[k][j-1], x[k+1][j-1] <= last[k][j-1]) ),If( (Or(q[k+1][j-1] == ControlLocation.start,q[k+1][j-1] == ControlLocation.check)), x[k+1][j-1] == x[k][j-1] + t1, x[k+1][j-1] == x[k][j-1] ) ) )
			
			ts.append( And( q[k+1][j-1] == q[k][j-1], first[k+1][j-1] == first[k][j-1], last[k+1][j-1] == last[k][j-1], Implies( (q[k][j-1] == ControlLocation.start), And(x[k][j-1] <= last[k][j-1], x[k+1][j-1] <= last[k][j-1]) ),  x[k+1][j-1] == x[k][j-1] + t1 ) )
			
			#ts.append( And( q[k+1][j-1] == q[k][j-1], Implies( (q[k][j-1] == ControlLocation.start), x[k][j-1] + t2 <= last[k][j-1] ),If( (Or(q[k+1][j-1] == ControlLocation.start,q[k+1][j-1] == ControlLocation.check)), x[k+1][j-1] == x[k][j-1] + t1, x[k+1][j-1] == x[k][j-1] ) ) )
			
		ts.append( t1 > 0 )
		ts.append( g[k+1] == g[k] )
		p = And( ts )
		#p = Exists([delta], ForAll([t2], Implies(And(t2 >= 0, t2 <= t1), p) ) )
		#p = Exists([t1], ForAll([t2], Implies(And(t2 >= 0, t2 <= t1), p) ) )
		#p = Exists([t1], p)
		
	if pmode == sats_3loc:
		for j in range(1,Nv+1):
			#ts.append( And( q[k+1][j-1] == q[k][j-1], x[k+1][j-1] >= x[k][j-1] + a * t1, x[k+1][j-1] <= x[k][j-1] + b * t1, Implies( (q[k][j-1] == ControlLocation.base), x[k+1][j-1] <= LB )  ) )
			ts.append( And( q[k+1][j-1] == q[k][j-1], Implies( (q[k][j-1] == ControlLocation.base), And(x[k][j-1] <= LB, x[k+1][j-1] <= LB) ), If( q[k][j-1] == ControlLocation.base, And(x[k+1][j-1] >= x[k][j-1] + a * t1, x[k+1][j-1] <= x[k][j-1] + b * t1), x[k+1][j-1] == x[k][j-1] ) ) )

		ts.append( t1 > 0 )
		p = And( ts )
		#p = Exists([delta], ForAll([t2], Implies(And(t2 >= 0, t2 <= t1), p) ) )
		#p = Exists([t1], ForAll([t2], Implies(And(t2 >= 0, t2 <= t1), p) ) )
		p = Exists([t1], p)

	if pmode == mux:
		p = False # no time transition (identity)
	
	print "Time transition:"
	p = simplifyBetterConj( p ).as_expr()
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
	
	
	print initList
	
	initAll = []
	for i  in range(1,Nv+1):
		initAll.extend( initList[i-1] )
	
	for i in range(1,Nv+1):
		theta.append( [] )
		theta[i-1] = []
		for j in range(1,Nv+1):
			theta[i-1].append( [] )
			if i != j:
				if pmode == fischer or pmode == fischer_aux or pmode == mux:
					#theta[i-1].append( And(initList[i-1], initList[j-1], globalInit) )
					theta[i-1][j-1] = And(And(initList[i-1]), And(initList[j-1]), globalInit) # TODO: PROJECT AWAY NON-I,J
					#theta[i-1][j-1] = And(And(initList), globalInit) # TODO: PROJECT AWAY NON-I,J
					#theta[i-1][j-1] = simplify(And(And( initAll ), globalInit))
				if pmode == sats_3loc:
					#theta[i-1].append( And(initList[i-1], initList[j-1]) )
					theta[i-1][j-1] = initList
			else:
				theta[i-1].append( [] )
	
	print theta

	print "loop until convergence. \n"
	change = 1
	index = 0

	while True:
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
		 			theta[i-1][j-1] = simplifyBetterConj( theta[i-1][j-1] ).as_expr()
					cList.append( theta[i-1][j-1] )
		conj = simplify( And(conj, And(cList) ) )
		print "Done building conjunct"
		conj = simplifyBetterConj( conj ).as_expr()
		print "Done simplifying conjunct"
		
		fileWrite(theta[0][1], "quant-ii-" + str(pmode) + "-iteration-" + str(index) + ".smt")

		fileWrite(conj, "quant-ii-" + str(pmode) + "-iteration-" + str(index) + "-conj.smt")
		
		if not change:
			break

		#print "conj start:"
		#print simplify(conj)
		#print "conj start end"

		print "start delta"
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
					
					bounds = []
					if pmode == mux:
						bounds = [q[0][i-1], q[0][j-1], gx[0]] # eliminate pre-state variable names
					if pmode == fischer:
						bounds = [q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], g[0]] # eliminate pre-state variable names
						#bounds = []
						#bounds = [q[0][i-1], x[0][i-1], g[0]]
					if pmode == fischer_aux:
						bounds = [q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], first[0][i-1], first[0][j-1], last[0][i-1], last[0][j-1], g[0]] # eliminate pre-state variable names
					if pmode == sats_3loc:
						#bounds = [q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], barray[0][i-1], barray[0][j-1]] # eliminate pre-state variable names
						bounds = [q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1]] # eliminate pre-state variable names
					
					#bounds.append( q[0][((j+1) % Nv)-1] )
					#bounds.append( x[0][((j+1) % Nv)-1] )
					
					bounds.extend( othersVarsPrePost_ii(i,j) ) # eliminate all other process variables (e.g., if looking at theta[0][1], eliminate vars of any process > 2)
					#print "others(" + str(i) + ", " + str(j) + "):" + str(othersVarsPrePost_ii(i,j))
					
					bounds.append( N )
					#bounds.extend( [N, x[1][0]] )
					#if pmode == fischer_aux:
					#	bounds.append( A )
					#	bounds.append( B )
				
					ts = []
					for m in range(1,Nv+1):
						#delta[i][j] = Or( delta[i][j], (succ(tr[m], conj) forsome others_vars[i][j]) )
						print "step"
						ts.extend( stepTransition(0, m) )
						
						# TODO NEXT: CAN WE INTERLEAVE THE Q.E. STEP HERE? E.G., ADD 1 TRANSITION, DO Q.E., REPEAT
						
					for tidx in range(len(ts)):
						s.push()
						s.add( And(conj, ts[tidx] ) )
						if s.check() == unsat: # transition not enabled, don't add it
							print "not adding: " + str(tidx)
							print ts[tidx]
							ts[tidx] = False # remove transition
						else:
							print "adding: " + str(tidx)
							#delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], And( conj, Or( ts ) ) ) )

							# do the step transition FOR EACH process m
							#delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], And( conj, Or( ts ) ) ) )
							#delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], And( conj, ts[tidx] ) ) )
							#delta[i-1][j-1] = computePost(delta[i-1][j-1], bounds, index)
							#delta[i-1][j-1] = Or( delta[i-1][j-1], computePost( And( conj, Or( ts ) ), bounds, index) )
							#delta[i-1][j-1] = Or( delta[i-1][j-1], computePost( And( conj, ts[tidx] ), bounds, index) )
							#delta[i-1][j-1] = Or( delta[i-1][j-1], And( conj, ts[tidx] ) )
							#fileWrite(delta[i-1][j-1], "quant-ii-" + str(pmode) + "-transition-" + str(index) + "-t" + str(tidx) + ".txt" )
						s.pop()
					ts.append( timeTransition(0) )
					delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], And( conj, Or( ts ) ) ) )
						
					# do the time transition ONCE for all processes, add it here
					if pmode == mux or pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
						bounds.append( t1 )
						timet = timeTransition(0)
						#timet = Exists([t1], timet)
						
						s.push()
						s.add( And(conj, timet ) )
						if s.check() == unsat: # transition not enabled, don't add it
							print "NO TIME ENABLED: not adding time\n\n\n\n\n\n\n"
							timet = False
						else:
							print s.model()
						s.pop()
						#return

						#delta[i-1][j-1] = Or( delta[i-1][j-1], And( conj, timet ) )
						#delta[i-1][j-1] = computePost(delta[i-1][j-1], [t1], index)
						
						#fileWrite(delta[i-1][j-1], "quant-ii-" + str(pmode) + "-transition-" + str(index) + "-t" + str(len(ts)) + ".txt" )
						
						#print "TIME-POST RESULT:"
						#print delta[i-1][j-1]
						#delta[i-1][j-1] = computePost(delta[i-1][j-1], bounds, index)
						print delta[i-1][j-1]
						#delta[i-1][j-1] = Or( delta[i-1][j-1], computePost(And( conj, timet ), [t1], index) )
						#delta[i-1][j-1] = Or( delta[i-1][j-1], And( conj, timet ))
						print delta[i-1][j-1]
						print bounds
						#delta[i-1][j-1] = computePost( delta[i-1][j-1], [q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], g[0], t1], index)
						delta[i-1][j-1] = computePost( And(And(assump),delta[i-1][j-1]), bounds, index)
						
						#if index >= 3:
						#	print delta[i-1][j-1]
						#	return
						
						# TODO: simplify better here
					
					# rename post-state to pre-state (x' -> x)
					kfrom = 1
					kto = 0
					subs = [] # collect all at once, otherwise we'd have to save local copies
					for idx in range(1,Nv+1):
						if pmode == fischer:
							subs.extend( [(q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (g[kfrom],g[kto])] )
						if pmode == fischer_aux:
							subs.extend( [(q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (g[kfrom],g[kto]), (first[kfrom][idx-1],first[kto][idx-1]), (last[kfrom][idx-1],last[kto][idx-1])] )
						if pmode == mux:
							subs.extend( [(q[kfrom][idx-1],q[kto][idx-1]), (gx[kfrom],gx[kto])] )
						if pmode == sats_3loc:
							#subs.extend( [(q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]), (barray[kfrom][idx-1],barray[kto][idx-1])] )
							subs.extend( [(q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1])] )
					delta[i-1][j-1] = simplify( substitute( delta[i-1][j-1], subs ) )

					print "TRANSITION(" + str(i) + ", " + str(j) + ")"
					#delta[i-1][j-1] = simplifyBetterConj( delta[i-1][j-1] ).as_expr()

		# add new states
		newtheta = []
		for i in range(1,Nv+1):
			newtheta.append( [] )
			newtheta[i-1] = []
			for j in range(1,Nv+1):
				newtheta[i-1].append( [] )
				if i != j:
					if i != 1 or j != 2:
						#print "replacing: " + str(i) + "," + str(j)
						kfrom = 0
						kto = 0
						ifrom = 1
						jfrom = 2
						
						# hard copy
						ctx2 = Context()
						cexpr = delta[0][1]
						copied = cexpr.translate(ctx2)
						cexpr = copied.translate(ctx)

						delta[i-1][j-1] = cexpr
						#delta[i-1][j-1] = delta[0][1] # copy (pointer...)
						
						subs = [] # use a list to do all the substitutions at once (otherwise we need to temporarily save them, but z3's substitute function will do this for us if we pass them all to it)
						
						if i != ifrom:
							#print "doing i: " + str(i) + "," + str(ifrom)
							subs.append( (q[kfrom][ifrom-1],q[kto][i-1]) )
							
							if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
								subs.append( (x[kfrom][ifrom-1],x[kto][i-1]) )
								
								
							if pmode == fischer_aux:
								subs.append( (last[kfrom][ifrom-1],last[kto][i-1]) )
								subs.append( (first[kfrom][ifrom-1],first[kto][i-1]) )
						if j != jfrom:
							#print "doing j: " + str(j) + "," + str(jfrom)
							subs.append( (q[kfrom][jfrom-1],q[kto][j-1]))
							
							if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
								subs.append( (x[kfrom][jfrom-1],x[kto][j-1]) )
							
							if pmode == fischer_aux:
								subs.append( (last[kfrom][jfrom-1],last[kto][j-1]) )
								subs.append( (first[kfrom][jfrom-1],first[kto][j-1]) )
						#print subs
						
						if len(subs) == 1: # varargs edge case
							delta[i-1][j-1] = substitute(delta[i-1][j-1], subs[0])
						else:
							delta[i-1][j-1] = substitute(delta[i-1][j-1], subs)
					fileWrite(delta[i-1][j-1], "theta_replace-iter" + str(index) + "ij" + str(i) + str(j) + ".smt")
					
					newtheta[i-1][j-1] = simplify( Or(theta[i-1][j-1], delta[i-1][j-1]) )
					
					#newtheta[i-1][j-1] = computePost(newtheta[i-1][j-1], othersVarsPrePost_ii(i,j), index) # ensure all other vars projected away
					#print newtheta[i-1][j-1]

		# check for change
		change = False
		print "fixpoint check"
		for i in range(1,Nv+1):
			for j in range(1,Nv+1):
				if i != j:
					s.push()
					s.add( Not(theta[i-1][j-1] == newtheta[i-1][j-1]) )
					res = s.check()
					unequal = True
					if res == unsat: # proved 2 expressions are equal
						unequal = False
					s.pop()
					change = change or unequal
					theta[i-1][j-1] = newtheta[i-1][j-1]
		
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
	#print theta[0][1]
	
	print "finished split invariant computation after " + str(index) + " iterations. \n"
	
	print "\nchecking for violations\n";

	# step 4: check for violation 
	# i.e., check if [(/\i,j: i \neq j: theta(i,j)) & auxc -> prop]
	# i.e., check if (/\i,j: i \neq j: theta(i,j)) & auxc & not(prop) is satisfiable
	qf = Function('qf', IntSort(), ControlLocation)	
	if pmode == mux:
		gxf = Int('gxf')
	if pmode == sats_3loc:
		xf = Function('xf', IntSort(), RealSort())
		bf = Function('bf', IntSort(), IntSort())
	if pmode == fischer or pmode == fischer_aux:
		xf = Function('xf', IntSort(), RealSort())
		gf = Int('gf')
	if pmode == fischer_aux:
		lastf = Function('lastf', IntSort(), RealSort())
		firstf = Function('firstf', IntSort(), RealSort())

	i = 1
	j = 2

	kfrom = 0
	iidx = Int('i')
	jidx = Int('j')
	
		
	if pmode == mux:
		quant = simplify( substitute(theta[i-1][j-1], (q[kfrom][i-1], qf(iidx) ), (q[kfrom][j-1], qf(jidx) ), (gx[kfrom],gxf ) ) )
	if pmode == fischer:
		quant = simplify( substitute(theta[i-1][j-1], (q[kfrom][i-1], qf(iidx) ), (q[kfrom][j-1], qf(jidx) ), (x[kfrom][i-1], xf(iidx) ), (x[kfrom][j-1], xf(jidx) ), (g[kfrom],gf ) ) )
	if pmode == fischer_aux:
		quant = simplify( substitute(theta[i-1][j-1], (q[kfrom][i-1], qf(iidx) ), (q[kfrom][j-1], qf(jidx) ), (x[kfrom][i-1], xf(iidx) ), (x[kfrom][j-1], xf(jidx) ), (g[kfrom],gf ), (last[kfrom][i-1], lastf(iidx) ), (last[kfrom][j-1], lastf(jidx) ), (first[kfrom][i-1], firstf(iidx) ), (first[kfrom][j-1], firstf(jidx) ) ) )
	if pmode == sats_3loc:
		#quant = simplify( substitute(theta[i-1][j-1], (q[kfrom][i-1], qf(iidx) ), (q[kfrom][j-1], qf(jidx) ), (x[kfrom][i-1], xf(iidx) ), (x[kfrom][j-1], xf(jidx) ), (barray[kfrom][i-1], bf(iidx) ), (barray[kfrom][j-1], bf(jidx) ) ) )
		quant = simplify( substitute(theta[i-1][j-1], (q[kfrom][i-1], qf(iidx) ), (q[kfrom][j-1], qf(jidx) ), (x[kfrom][i-1], xf(iidx) ), (x[kfrom][j-1], xf(jidx) ) ) )
	#print quant
	
	
	quant = ForAll([iidx, jidx], Implies(indexBounds_ii(iidx,jidx), quant))
	
	viol = And(quant, Not(safetyQ(iidx, jidx, qf) ))

	s.push()
	s.add(viol)
	res = s.check()
	s.pop()
	
	#print viol
	#print res
	
	print Not(safetyQ(iidx, jidx, qf) )
	
	if res == sat:
		print "!!!!! violation !!!!!\n"
		#print viol
		print "a satisfying assignment\n"
		print s.model()
	else:
		print "No violation found\n"


	quant = simplifyResult( quant )
	
	fileWrite(quant, "quant-ii-" + str(pmode) + ".smt")
	
	














def computePost(prop,bounds,round):
	print "step done"
	print "bounds " + str(bounds)

	rest = simplifyBetter( prop )
	#rest = simplifyBetter( delta[i-1][j-1] )
	#rest = simplifyBetterConj( delta[i-1][j-1] )

	print "before unique:"  + str(len(rest))

	newList = []

	print "at bound elimination for iteration " + str(round)
	print bounds
	print datetime.now()
	sidx = 0

	scount = len(rest)

	for subr in rest:
		#print subr.as_expr()
		if sidx % 100 == 0:
			print "Iteration " + str(round) + ": on subterm " + str(sidx) + " of " + str(scount)
		sidx = sidx + 1

		tgoal = Goal()

		#tgoal.add( And(assump) )
		#tgoal.add( N == Nv)

		#tgoal.add( Exists(bounds, And(And(assump), subr.as_expr() ) ) )
		tgoal.add( Exists(bounds, subr.as_expr() ) )
		#ttac = With(Tactic('qe'),  eliminate_variables_as_block=True) # qe_nonlinear=True
		ttac = Then(Repeat(Tactic('ctx-simplify')), Repeat(Tactic('simplify')), Repeat('symmetry-reduce'), With(Tactic('qe'),  eliminate_variables_as_block=False)) # qe_nonlinear=True

		tr = ttac(tgoal)
		tr = simplifyBetter( tr.as_expr() )
		#print tr
		for gt in tr:
			#print gt.as_expr()
			newList.append( simplifyBetter( gt.as_expr() ).as_expr() )
	newstates = Or(newList)
	return newstates




















def split_inv_tlv_i(prop,Nv,auxc):
# prop is correctness property
# N is the number of processes in the system
#  auxc is an invariant defining auxiliary variables used in the proof
	theta = []
	for i in range(1,Nv+1):
		theta.append( [] )
		if pmode == sats_3loc:
			theta[i-1] = And(initList[i-1])
		else:
			theta[i-1] = And(And(initList[i-1]), globalInit)

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
		conj = simplify( And(conj, And(cList) ) )
		print "Done building conjunct"
		
		conj = simplifyBetterConj( conj ).as_expr()
		print "Done simplifying conjunct"

		# compute delta to be added to theta(i,j)
		delta = []
		for i in range(1,Nv+1):
			delta.append( [] )
			delta[i-1] = False # start with false (identity since we're adding disjuncts)
			#print delta[i-1][j-1]

			# only do 1 iteration, copy delta[i-1][j-1] to the others
			if not (i == 1):
				continue


			bounds = []
			if pmode == mux:
				bounds = [q[0][i-1], gx[0]] # eliminate pre-state variable names
			if pmode == fischer:
				#bounds = [t1,q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], g[0]] # eliminate pre-state variable names
				bounds = [q[0][i-1], x[0][i-1], g[0]] # eliminate pre-state variable names
			if pmode == fischer_aux:
				#bounds = [t1,q[0][i-1], q[0][j-1], x[0][i-1], x[0][j-1], g[0]] # eliminate pre-state variable names
				bounds = [q[0][i-1], x[0][i-1], first[0][i-1], last[0][i-1], g[0]] # eliminate pre-state variable names
			if pmode == sats_3loc:
				#bounds = [q[0][i-1], x[0][i-1], barray[0][i-1]] # eliminate pre-state variable names
				bounds = [q[0][i-1], x[0][i-1]] # eliminate pre-state variable names

			bounds.extend( othersVarsPrePost_i(i) ) # eliminate all other process variables (e.g., if looking at theta[0][1], eliminate vars of any process > 2)
			print "others(" + str(i) + "):" + str(othersVarsPrePost_i(i))

			if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
				bounds.append( t1 )
				#ts.append( timeTransition(0) )
				# do the time transition ONCE for all processes, add it here
				delta[i-1] = Or( delta[i-1], And( conj, timeTransition(0) ) )

			for m in range(1,Nv+1):
				#delta[i][j] = Or( delta[i][j], (succ(tr[m], conj) forsome others_vars[i][j]) )
				print "step"
				#ts.extend( stepTransition(0,m) )
				ts = stepTransition(0, m)


				# TODO NEXT: CAN WE INTERLEAVE THE Q.E. STEP HERE? E.G., ADD 1 TRANSITION, DO Q.E., REPEAT

				for tidx in range(len(ts)):
					s.push()
					s.add( And(conj, ts[tidx] ) )
					if s.check() == unsat: # transition not enabled, don't add it
						ts[tidx] = False
					print tidx
					s.pop()

				#delta[i-1][j-1] = simplify( Or( delta[i-1][j-1], And( conj, Or( ts ) ) ) )

				# do the step transition FOR EACH process m
				delta[i-1] = simplify( Or( delta[i-1], And( conj, Or( ts ) ) ) )


			print "simplifying goal"

			rest = simplifyBetter( delta[i-1] )

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


				#tgoal.add( And(assump) )
				#bounds.extend( [N, x[1][0] ])
				bounds.append( N )
				#tgoal.add( 
				tgoal.add( Exists(bounds, And(And(assump), subr.as_expr() ) ) )
				#tgoal.add( Exists(bounds, subr.as_expr() ) )

				#ttac = With(Tactic('qe'),  eliminate_variables_as_block=True) # qe_nonlinear=True
				ttac = With(Tactic('qe'),  eliminate_variables_as_block=False) # qe_nonlinear=True

				tr = ttac(tgoal)
				tr = simplifyBetter( tr.as_expr() )
				#print tr
				for gt in tr:
					#print gt.as_expr()
					newList.append( simplifyBetter( gt.as_expr() ).as_expr() )

				#newList.append( simplify(tr.as_expr() ) )

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
				if pmode == sats_3loc:
					delta[i-1] = simplify( substitute( delta[i-1], (q[kfrom][idx-1],q[kto][idx-1]), (x[kfrom][idx-1],x[kto][idx-1]) ) )
				delta[i-1] = simplifyBetterConj( delta[i-1] ).as_expr()

			print "TRANSITION(" + str(i) + ")"


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
				if pmode == sats_3loc:
					delta[i-1] = substitute( delta[ifrom-1], (q[kfrom][ifrom-1],q[kto][ito-1]), (x[kfrom][ifrom-1],x[kto][ito-1])  )

			newtheta[i-1] = simplify( Or(theta[i-1], delta[i-1]) )
			#print newtheta[i-1][j-1]

		# check for change
		change = False
		for i in range(1,Nv+1):
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
	if pmode == sats_3loc:
		xf = Function('xf', IntSort(), RealSort())
	if pmode == fischer_aux:
		lastf = Function('lastf', IntSort(), RealSort())
		firstf = Function('firstf', IntSort(), RealSort())
	
	
	i = 1
	
	
	kfrom = 0
	iidx = Int('i')
	jidx = Int('j')
	
		
	if pmode == mux:
		quant = simplify( substitute(delta[i-1], (q[kfrom][i-1], qf(iidx) ), (gx[kfrom],gxf ) ) )
	if pmode == fischer:
		quant = simplify( substitute(delta[i-1], (q[kfrom][i-1], qf(iidx) ), (x[kfrom][i-1], xf(iidx) ), (g[kfrom],gf ) ) )
	if pmode == fischer_aux:
		quant = simplify( substitute(delta[i-1], (q[kfrom][i-1], qf(iidx) ), (x[kfrom][i-1], xf(iidx) ), (g[kfrom],gf ), (last[kfrom][i-1], lastf(iidx) ), (first[kfrom][i-1], firstf(iidx) ) ) )
	if pmode == sats_3loc:
		quant = simplify( substitute(delta[i-1], (q[kfrom][i-1], qf(iidx) ), (x[kfrom][i-1], xf(iidx) ) ) )
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


	#print quant
	fileWrite(quant, "quant-i-" + str(pmode) + ".smt")




def fileWrite(quant, name):
	fptr = open(name, 'w')
	if Pv == 1:
		qstr = quant.sexpr().replace("=>","implies").replace("qf","q").replace("gxf","x").replace("xf","x").replace("gf","g").replace("<","&lt;").replace(">","&gt;").replace("(= g 1)","(= g i)").replace("(= g 2)","(not (= g i))").replace("(= g 0)", "(not (= g i))").replace("lastf","last").replace("firstf","first");
	elif Pv == 2:
		qstr = quant.sexpr().replace("=>","implies").replace("qf","q").replace("gxf","x").replace("xf","x").replace("gf","g").replace("<","&lt;").replace(">","&gt;").replace("(= g 1)","(= g i)").replace("(= g 2)","= g j").replace("(= g 3)", "(and (not (= g i)) (not (= g j)))").replace("(= g 0)", "(and (not (= g i)) (not (= g j)))").replace("lastf","last").replace("firstf","first");
	else:
		qstr = quant.sexpr().replace("qf","q").replace("gxf","x").replace("xf","x").replace("gf","g").replace("<","&lt;").replace(">","&gt;").replace("(= g 1)","(= g i)").replace("(= g 2)","(= g j)").replace("(= g 3)", "(and (not (= g i)) (not (= g j)))").replace("(= g 0)", "(and (not (= g i)) (not (= g j)))").replace("lastf","last").replace("firstf","first");
	#fptr.write( quant.sexpr().replace("bf","b").replace("qf","q").replace("gxf","x").replace("xf","x").replace("gf","g").replace("<","&lt;").replace(">","&gt;").replace("= g 1","= g i").replace("(= g 2)","(not (= g i))").replace("(= g 3)", "(not (= g i))").replace("(= g 0)", "(not (= g i))") )
	fptr.write( qstr )
	fptr.close()





































def safetyQ(i,j,q):
	if pmode == fischer or pmode == fischer_aux or pmode == mux:
		return ForAll([i,j], Implies( indexBounds_ii(i,j), Or( q(i) != ControlLocation.cs, q(j) != ControlLocation.cs) ))
	if pmode == sats_3loc:
		return True

def safety(Nv):
	sList = []
	for i in range(1,Nv+1):
		nList = []
		for j in range(1,Nv+1):
			if i == j:
				continue
			#sList.append( Implies( q[0][i-1] == ControlLocation.cs, q[0][j-1] != ControlLocation.cs ) )
			#sList.append( Or(q[0][i-1] != ControlLocation.cs, q[0][j-1] != ControlLocation.cs ) )
			if pmode == fischer or pmode == fischer_aux or pmode == mux:
				nList.append( q[0][j-1] != ControlLocation.cs )
		if pmode == fischer or pmode == fischer_aux or pmode == mux:
			sList.append( Implies(q[0][i-1] == ControlLocation.cs, And(nList) ) )
	if len(sList) > 0:
		return And( sList )
	else:
		return True


def indexBounds_ii(i,j):
	return And( 1 <= i, i <= N, 1 <= j, j <= N, i != j)
	

def indexBounds_i(i):
	return And( 1 <= i, i <= N)



def universalGuard(g,i,j,k):
	ov = othersVars(i)
	gList = []
	for n in range(1,Nv+1):
		if n != i:
			# todo: change if using this elsewhere (only for sats_3loc)
			grep = simplify( substitute(g, (q[k][j-1], q[k][n-1] ), (x[k][j-1], x[k][n-1] ) ) )
			gList.append( grep )
	return And( gList )


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
			#if pmode ==  pmode == sats_3loc:
				#ov.extend( [ barray[0][i-1] ] )
	return ov
	

def othersVars(m):
	ov = []
	for i in range(1,Nv+1):	
		if i != m:
			if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
				ov.extend( [q[0][i-1], x[0][i-1] ] )
			if pmode == fischer_aux:
				ov.extend( [first[0][i-1], last[0][i-1]] )
			if pmode == mux:
				ov.extend( [q[0][i-1]] )
			#if pmode == sats_3loc:
			#	ov.extend( [ barray[0][i-1]] )
	return ov
	

def uniqueElements(seq):
   # Not order preserving    
   set = Set(seq)
   return list(set)
  

def othersVarsPrePost_ii(m,n):
	ov = []
	for i in range(1,Nv+1):	
		if i != m and i != n:
			if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
				ov.extend( [q[0][i-1], x[0][i-1]] )
				ov.extend( [q[1][i-1], x[1][i-1]] )
			if pmode == fischer_aux:
				ov.extend( [first[0][i-1], last[0][i-1]] )
				ov.extend( [first[1][i-1], last[1][i-1]] )
			if pmode == mux:
				ov.extend( [q[0][i-1]] )
				ov.extend( [q[1][i-1]] )
			#if pmode == sats_3loc:
				#ov.extend( [barray[0][i-1]] )
				#ov.extend( [barray[1][i-1]] )
	return ov
	
def othersVarsPrePost_i(m):
	ov = []
	for i in range(1,Nv+1):	
		if i != m:
			if pmode == fischer or pmode == fischer_aux or pmode == sats_3loc:
				ov.extend( [q[0][i-1], x[0][i-1]] )
				ov.extend( [q[1][i-1], x[1][i-1]] )
			if pmode == fischer_aux:
				ov.extend( [first[0][i-1], last[0][i-1]] )
				ov.extend( [first[1][i-1], last[1][i-1]] )
			if pmode == mux:
				ov.extend( [q[0][i-1]] )
				ov.extend( [q[1][i-1]] )
			#if pmode == sats_3loc:
				#ov.extend( [barray[0][i-1]] )
				#ov.extend( [barray[1][i-1]] )
	return ov

def simplifyResult(expr):
	g = Goal()
	g.add( expr )
	#, Repeat('ctx-simplify')
	#tac = Repeat(Then( Repeat(Tactic('propagate-values')), Repeat('propagate-ineqs'), Repeat('normalize-bounds'), Repeat('elim-uncnstr'), Repeat('solve-eqs'), Repeat('purify-arith'), Repeat('symmetry-reduce'), Repeat('simplify'), Repeat('max-bv-sharing')))
	tac = Tactic('ctx-solver-simplify')
	
	#tac = Repeat(Then(Repeat('max-bv-sharing'),Tactic('simplify'), Tactic('elim-term-ite'), Tactic('ctx-simplify'), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('ctx-simplify'))))
	
	return tac( g ).as_expr()

def simplifyBetterConj(expr):
	g = Goal()
	g.add( expr )
	#tac = Repeat(Then( Tactic('lia2pb'), Tactic('simplify'), Tactic('ctx-simplify'), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat('normalize-bounds')))
	#tac = Then( Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')))
	
	
	
#gconj = Goal()
#gconj.add( conj )
# apply a tactic to drastically simplify conj
#tconj = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), Repeat(Tactic('simplify')))
#tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))
#tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')), Repeat(Tactic('ctx-solver-simplify')))


#tconj = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify')), Tactic('ctx-solver-simplify'))
#tconj = Tactic('ctx-solver-simplify')

#tconj = Then( Tactic('propagate-values'), Tactic('propagate-ineqs'), Tactic('ctx-solver-simplify'))

#tconj = Then( Repeat(Tactic('simplify')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat( OrElse(Tactic('split-clause'), Tactic('skip') ) ), Tactic('ctx-solver-simplify'))

	#tac = Then(With('simplify', arith_lhs=True, som=True), 'normalize-bounds', 'propagate-values', 'propagate-ineqs')


#conj = tconj( gconj ).as_expr()

	#tac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('normalize-bounds')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')), Tactic('ctx-solver-simplify'))
	tac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('simplify')))
	#tac = Tactic('ctx-solver-simplify')
	#g.add( And( assump ) ) # need to do this, otherwise ctx-solver-simplify will drop results
	
	#tac = Then(Tactic('lia2pb'), Tactic('ctx-solver-simplify'))
	#tac = Then(Tactic('lia2pb'), Tactic('ctx-simplify'))
	
	#tac = Tactic('skip')
	
	#tac = Repeat(Then( Tactic('lia2pb'), Tactic('simplify'), Tactic('ctx-simplify'), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat('normalize-bounds')))
	
	
	
	return tac.apply( g )

def simplifyBetter(expr):
	g = Goal()
	g.add( expr )
	
	#tac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify')), Tactic('ctx-solver-simplify'))
	
	#tac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('ctx-solver-simplify')))
	
	#tac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')))
	
	#stac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))

	#stac = Repeat(Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify'))))
	#stac = Repeat(Then( Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify'))))


	#tac = Repeat(Then( Tactic('propagate-values'), Tactic('propagate-ineqs')))

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
	#tac = Then( Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')))

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
	
	#tac = Tactic('skip')
	
	#tac = Then(Repeat('simplify'),Repeat('max-bv-sharing'))
	
			
			
			
	#tac = Then( Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))
			
	
	#tac = Repeat(Then( Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), Repeat(Tactic('simplify'))))


	#stac = Then( Tactic('propagate-values'), Tactic('propagate-ineqs'))
	
	#print expr
	#tac = Then(Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('simplify')))
	
	#tac = Then(Repeat('max-bv-sharing'),Tactic('simplify'), Tactic('elim-term-ite'), Tactic('ctx-simplify'), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat('max-bv-sharing'),Repeat(Tactic('ctx-simplify')))
	
	#tac = Tactic('ctx-simplify')
	
	tac = Repeat(Then(Repeat('max-bv-sharing'),Tactic('simplify'), Tactic('elim-term-ite'), Tactic('ctx-simplify'), Repeat(Tactic('elim-and')), Repeat(Tactic('propagate-values')), Repeat(Tactic('propagate-ineqs')), OrElse(Tactic('split-clause'), Tactic('skip')), Repeat(Tactic('ctx-simplify'))))	
	#tac = Tactic('ctx-solver-simplify')
	
	return tac( g )
	

def toCnf(expr):
	g1 = Goal()
	g1.add( expr )
	#'(then (! simplify :elim-and true) elim-term-ite tseitin-cnf)'
	tac1 = Then( With(Tactic('simplify'), elim_and=True), Tactic('elim-term-ite'), With(Tactic('tseitin-cnf'), distributivity=False))
	rcnf = tac1( g1 )
	return rcnf.as_expr()


if Pv == 1:
	split_inv_tlv_i(safety(Nv),Nv,True)
elif Pv == 2:
	split_inv_tlv_ii(safety(Nv),Nv,True)
