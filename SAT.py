#!/bin/python

# Required for sys.exit ( )
import sys

# Required for random.choice ( )
import random

# Required for getcwd ( ) , walk () , path.join ()
import os

# The algorithms that the SAT solver is able to use
ALGO = [ 'CHAOS' , 'GSAT' , 'GSAT_WALKS' , 'WSAT' ]

DEBUG = True

LINEWIDTH = 30

def main ( argv ) :

  asciiArt ( )

  print '\n  Debugging is: ' + ( 'EN' if DEBUG else 'DIS' ) + 'ABLED\n\n ',

  for i in xrange ( 0 , LINEWIDTH ) : print '-',
  print ''
  argc = len ( argv )

  if argc == 0 :
    file = getFile ( )
    algo = getAlgo ( )
  elif argc == 1 :
    if argv [ 0 ] == '-std':
      file = getFromStd ();
    else:
      file = getFile ( argv [ 0 ] )
      print '\n  Using filename given as argument: ' + file
    algo = getAlgo ( )
  else :
    file = argv [ 0 ]
    algo = getAlgo ( argv [ 1 ] )

  try:
    fh = open ( file , "r" ) 
  except IOError as e:
    print '\n  ' + e [ 1 ] + '\n'
    sys.exit ( )

  lines = fh.readlines ( )

  print '\n  Reading from ' + str ( file ) + ' - ' + str ( len ( lines ) ) + ' lines\n\n ',
  for i in xrange ( 0 , LINEWIDTH ) : print '-',
  print ''

  problem = None
  nvar = 0
  symbols = [ ]
  nclause = 0
  clauses = [ ]

  n = 1
  for line in lines :

    line = line.strip ( )

    # Lines starting with c are comments
    if line.startswith ( 'c' ) or line == '' :
      n = n + 1
      continue

    # The line starting with p contains problem stats
    # The first part indicates the clausal formc
    # The second part indicates the number of variables
    # The third part indicates the number of clauses 
    if line.startswith ( 'p' ) :

      if problem == None :

        # Read the problem details
        problem = line.split ( )
        problem.pop ( 0 )

        nproblem = len ( problem )
        if nproblem < 3 :

          print '  Error [ line ' + str ( n ) + ' ]: ' + str ( nproblem ) + ' part' + ( 's' if nproblem != 1 else '' ) + ' found, expecting 3'
          break

        else :

          if problem [ 0 ].lower ( ) != 'cnf' :
            print '  Error [ line ' + str ( n ) + ' ]: Unknown problem type "' + str ( problem [ 0 ] ) + '" - known types: [ cnf ]' 
            break

          try :

            nvar = int ( problem [ 1 ] )
            if nvar <= 0 : raise ValueError

          except ValueError:

            print '  Error [ line ' + str ( n ) + ' ]: Number of variables must be a positive integer - "' + str ( problem [ 1 ] ) + '" given'
            break

          try :

            nclause = int ( problem [ 2 ] )
            if nclause <= 0 : raise ValueError

          except ValueError:

            print '  Error [ line ' + str ( n ) + ' ]: Number of clauses must be a positive integer - "' + str ( problem [ 1 ] ) + '" given'
            break

      else :

        # A second occurrence of a problem definition doesn't make sense 
        print '  Error [ line ' + str ( n ) + ' ]: Problem already set'
        break

      n = n + 1
      continue

    else :

      # There should only be one line starting with P
      if problem == None : 
        print '  Error [ line ' + str ( n ) + ' ]: Clause given but no problem details set'
        break

      if line.endswith ( '0' ) :

        # Add to list of clauses
        line = line [ : -1 ] .strip ( )
        clauses.append ( line )

        # Strip negations so that the list of literals includes both negated and non symbols
        syms = line.replace ( '-' , '' ).split ( ' ' )
        for sym in syms :
          if not sym in symbols : symbols.append ( sym )

      else:

        print '  Error [ line ' + str ( n ) + ' ]: Clause did not end with 0 terminator'

    #print str ( n ) + line.strip ( )
    n = n + 1

  fh.close ( )

  nclausegiven = len ( clauses )
  if nclausegiven == 0 :
    print '  Error [ line ' + str ( n ) + ' ]: End of file reached but no clauses read'
    sys.exit ( )

  print '\n  ' + str ( nclausegiven ) + ' clauses given'
  print ' ' , clauses

  nsymgiven = len ( symbols )
  if nsymgiven != nvar :
    print '  Error [ line ' + str ( n ) + ' ]: End of file reached and number of variables read doesn\'t match the expected ' + str ( nvar )
    sys.exit ( )

  print '\n  ' + str ( nsymgiven ) + ' variables given'
  print ' ' , symbols , '\n'

  print '  Using algorithm: ' + ALGO [ algo ] +'\n\n' ,

  #print {
  #  'CHAOS' : CHAOS ( clauses , nvar , 10 ) ,
  #  'GSAT' : GSAT ( clauses , nvar , 10 ,  10 ) ,
  #} .get ( ALGO [ algo ] )

  # Get algorithm options

  

  if ALGO [ algo ] == 'CHAOS' :
    print CHAOS ( clauses , nvar , 10 )
  elif ALGO [ algo ] == 'GSAT' :
    print GSAT ( clauses , nvar , 1 ,  10 )

  print '\n ' ,
  for i in xrange ( 0 , LINEWIDTH ) : print '-' ,
  print '\n'

  # Start solving attempts
  #print '  Result: ' + CHAOS ( clauses , nvar , 10 ) + '\n'





def randomInterpretation ( nvar ) :
  interp = { }
  for i in xrange ( 1 , nvar + 1 ) : interp [ str ( i ) ] = random.choice ( [ 0 , 1 ] ) 
  return interp







def CHAOS ( clauses , nvar , MAX_TRIES ) :

  # procedure CHAOS ( S )
  # input: set of clauses S
  # output: interpretation I such that I |= S or "Don't know"
  # parameters: positive integer MAX_TRIES
  # begin
  #   repeat MAX_TRIES times

  if DEBUG : print '  CHAOS (\n    clauses: ' + str ( clauses ) + ' ,\n    nvar: ' + str ( nvar ) + ' ,\n    MAX_TRIES: ' + str ( MAX_TRIES ) + '\n  )\n'

  if DEBUG : print '  Interpretation'

  for i in xrange ( 1 , MAX_TRIES ) :

  #     I := random interpretation

    I = randomInterpretation ( nvar )

    if DEBUG : print ' ' , prettyInterp ( I , False )

  #     if I |= S then return I

    if interpret ( clauses , len ( clauses ) , I ) [ 1 ] : return I

  #   return "Don't know"

  return "\n  Result: Don't know"

  # end






# An implemention of the GSAT algorithm

def GSAT ( clauses , nvar , MAX_TRIES , MAX_FLIPS ) :

  # procedure GSAT ( S )
  # input: set of clauses S
  # output: interpretation I such that I |= S or "Don't know"
  # parameters: integers MAX_TRIES , MAX_FLIPS
  # begin
  #   repeat MAX-TRIES times

  if DEBUG : print '  GSAT (\n    clauses: ' + str ( clauses ) + ' ,\n    nvar: ' + str ( nvar ) + ' ,\n    MAX_TRIES: ' + str ( MAX_TRIES ),
  if DEBUG : print ',\n    MAX_FLIPS: ' + str ( MAX_FLIPS ) + '\n  )\n'

  for i in xrange ( 1 , MAX_TRIES + 1 ) :

  #     I := random interpretation

    if DEBUG : print '  = = = = = Try ' + str ( i ) + ' of ' + str ( MAX_TRIES ) + ' = = = = = '

    I = randomInterpretation ( nvar )

    result = interpret ( clauses , len ( clauses ) , I )

    if DEBUG : print '\n  Random:', prettyInterp ( I ), 'satisfies ' + str ( result [ 0 ] ) + ' clause \n'

  #     if I |= S then return I

    if result [ 1 ] :
      if DEBUG : '  Randomly chosen interpretation satisfied all clauses!'
      return I

  #     repeat MAX_FLIPS times

    for j in xrange ( 1 , MAX_FLIPS ) :

  #       p := a variable such that flip ( I , p ) satisfies
  #            the maximal number of clauses in S

      # Clone the interpretation we're currently working with to test flip results
      tempI = I

      # Store the number of clauses satisfied by each flip
      flipresult = {}

      for var in tempI.keys ( ) :

        # Flip the variable
        tempI [ var ] = flip ( tempI [ var ] )

        # Test the interpretation
        result = interpret ( clauses , len ( clauses ) , tempI )
        satcount = result [ 0 ]

        if DEBUG : print '  Flipping ' + str ( var ) + ' would give: ' + prettyInterp ( tempI ) + ' and satisfy ' + str ( satcount ) + ' clause'

        if satcount in flipresult.keys ( ) :
          flipresult [ satcount ].append ( var )
        else:
          flipresult [ satcount ] = [ var ]

        # Flip it back
        tempI [ var ] = flip ( tempI [ var ] )

  #       I = flip ( I , p )

      # Find assignments that gave largest number of satisfied clauses
      vartoflip = max ( k for k , v in flipresult.iteritems ( ) )
      flipCandidates = flipresult [ vartoflip ]

      # Randomly pick one - could do this with some intelligence as to what's already been tried in a past run later
      vartoflip = random.choice ( flipCandidates )

      if DEBUG : print '\n  Flip candidates:', flipCandidates, ' - flipping ' + str ( vartoflip )

      I [ vartoflip ] = flip ( I [ vartoflip ] )

  #       if I |= S then return I

      result = interpret ( clauses , len ( clauses ) , I );

      if DEBUG : print '  ' + str ( result [ 0 ] ) + ' clause satisfied\n'

      if result [ 1 ] : return I

  #   return "Don't know"

  return "  Don't know"

  # end









def GSAT_WALKS ( clauses , nvar , MAX_TRIES , MAX_FLIPS , PI ) :

  # procedure GSATwithWalks ( S )
  # input: set of clauses S
  # output: interpretation I such that I |= S or "Don't know"
  # parameters: integers MAX_TRIES , MAX_FLIPS
  #             real number 0 <\ PI <\ 1 ( probability of a sideways move )
  # begin
  #   repeat MAX-TRIES times

  for i in xrange ( 1 , MAX_TRIES ) :

  #     I := random interpretation

    I = randomInterpretation ( nvar )

  #     if I |= S then return I

    if interpret ( clauses , len ( clauses ) , I ) [ 1 ] : return I

  #     repeat MAX_FLIPS times

    for j in xrange ( 1 , MAX_FLIPS ) :

  #       with probability PI
  #       p := a variable such that flip ( I , p ) satisfies
  #            the maximal number of clauses in S
  #       with probability 1 - PI
  #         randomly select p among all variables occurring in clauses false in I

      if random.random ( ) >= PI :

        # Clone the interpretation we're currently working with to test flip results
        tempI = I

        # Store the number of clauses satisfied by each flip
        flipresult = {}

        for var in tempI.keys ( ) :

          # Flip the variable
          tempI [ var ] = flip ( tempI [ var ] )

          # Test the interpretation
          result = interpret ( clauses , len ( clauses ) , tempI )
          satcount = result [ 0 ]
          if satcount in flipresult.keys ( ) :
            flipresult [ satcount ].append ( var )
          else :
            flipresult [ satcount ] = [ var ]

          # Flip it back
          tempI [ var ] = flip ( tempI [ var ] )

        vartoflip = max ( k for k , v in x.iteritems ( ) )

        I [ vartoflip ] = flip ( I [ vartoflip ] )

      else :


  #     I = flip ( I , p )

        I [ vartoflip ] = flip ( I [ vartoflip ] )

  #     if I |= S then return I

      if interpret ( clauses , len ( clauses ) , I ) [ 1 ] : return I

  #   return "Don't know"

  return "Don't know"

 # end











# An implemention of the WSAT algorithm

def WSAT ( clauses , nvar , MAX_TRIES , MAX_FLIPS ) :

  # procedure WSAT ( S )
  # input: set of clauses S
  # output: interpretation I such that I |= S or "Don't know"
  # parameters: integers MAX-TRIES , MAX-FLIPS
  # begin
  #   repeat MAX-TRIES times

  for i in xrange ( 1 , MAX_TRIES ) :

  #     I |= random interpretation

    I = randomInterpretation ( nvar )  

  #     if I |= S then return I

    if interpret ( clauses , len ( clauses ) , I ) [ 1 ] : return I

  #     repeat MAX-FLIPS times

    for j in xrange ( 1 , MAX_FLIPS ) :
      break;

  #       randomly select a clause C e S such that I |/= C
  #       randomly select a variable p in C
  #       I = flip ( I , p )

      I [ vartoflip ] = flip ( I [ vartoflip ] )

  #       if I |= S then return I

      if interpret ( clauses , len ( clauses ) , I ) [ 1 ] : return I

  #   return "Don't know"

  return "Don't know"

  # end





# Flips a value: 0 to 1 , 1 to 0

def flip ( var ) :
  return 0 if str ( var ) == '1' else 1




def solve ( nvar , clauses ) :

  # Initial interpretation of all zeros
  interp = { }
  for i in xrange ( 1 , nvar + 1 ) : interp [ str ( i ) ] = 0 

  print interp

  interpret ( clauses , len ( clauses ) , interp )

  # Flip a random var
  interp = flipRandIn ( interp )

  print interp

  interpret ( clauses , len ( clauses ) , interp )

  # Flip a random var
  interp = flipRandIn ( interp )

  print interp

  interpret ( clauses , len ( clauses ) , interp )


# Given an interpretation, flips the value of a literal assignment and returns the new interpretation
def flipRandIn ( interp ) :

  randvar = random.choice ( interp.keys ( ) )
  interp [ randvar ] = flip ( interp [ randvar ] )
  return interp


# Given a group of clauses, the number of clauses in the group and an interpretation, find the number of clauses
# satisfied by the interpretation, whether or not it was all of them and a string representation of the result
def interpret ( clauses , nclause , interp ) :

  #for i in xrange ( 0 , 14 ) : print '-',

  satcount = 0
  sat = [ ]
  unsat = [ ]

  for i in xrange ( 0 , nclause ) :

    result = interpretClause ( clauses [ i ] , interp )

    # Will be incremented if it was satisfiable
    satcount = satcount + result [ 1 ]

    #print "\n%-20s%-5s" % ( clauses [ i ] , result [ 1 ] )
    #for i in xrange ( 0 , LINEWIDTH ) : print '-',

  return ( satcount , str ( satcount ) == str ( nclause ) , '\nSatisfied ' + str ( satcount ) + ' of ' + str ( nclause ) + '\n' )




# Given a clause and interpretation, find the resultant truth assignments and whether the clause is satisfied by the assignment
def interpretClause ( clause , interp ) :

  # Make sure we are working with a list of clauses rather than a string containing spaces between literals
  if not isinstance ( clause , list ) : clause = clause.split ( ' ' )

  # Apply each assignment given in the interpretation
  for assign in interp.keys ( ) :

      # Replace literals with interpretation assignments
      # P is replaced with 1 if P = 1    -P is replaced with -1 if P = 1
      # P is replaced with 0 if P = 0    -P is replaced with -0 if P = 0
      clause = [ interp [ assign ] if str ( lit ) == str ( assign ) else
               ( '-' + str ( interp [ assign ] ) if str ( lit ) == '-' + str ( assign ) else lit )
               for lit in clause ]

      # Replace -0 with 1 and -1 with 0
      clause = [ '0' if str ( lit ) == '-1' else ( '1' if str ( lit ) == '-0' else lit ) for lit in clause ]

  # If a 1 is present then a literal has value 1 and so the clause is satisfied
  return ( clause , '1' in clause )






fileList = [];
onFile = 1;
onAlgo = 1;

def getFile ( arg = None ) :

  global fileList , onFile

  if arg != None :
    try:
      fh = open ( arg , "r" )
      return arg
    except IOError as e:
      print '\n  ' + e [ 1 ]

  print '\n  Listing .cnf files in ' , os.getcwd ( ) , '\n'

  for r , d , f in os.walk ( "." ) :
    for files in f:
      if files.endswith ( ".cnf" ):
        print "  %-3s%-50s" % ( str ( onFile ) , os.path.join ( r , files ) )
        onFile = onFile + 1
        fileList.append ( os.path.join ( r , files ) )

  filePicked = False
  picked = pickFile ( )
  if picked != False :
    return picked
  while not filePicked :
    picked = pickFile ( )
    if picked != False :
      filePicked = True

  return picked
  


def pickFile ( ) :

  wantFile = raw_input ( '\n  Enter a file number (or QUIT to exit): ' )

  if str ( wantFile ).upper ( ) == 'QUIT':
    print '\n  Goodbye\n'
    sys.exit ( )

  try :
    wantFile = int ( wantFile )
    if wantFile <= 0 : raise ValueError

  except ValueError:
    print '\n  Not an integer in the list'
    return False

  if wantFile > onFile - 1 : 
    print '\n  Not an integer in the list'
    return False  

  try:
    fh = open ( fileList [ wantFile - 1 ] , "r" )
    return fileList [ wantFile - 1 ]
  except IOError as e:
    print '\n  ' + e [ 1 ]
    return False





def getFromStd ( ) :

  data = sys.stdin.readlines()
  print "Counted", len(data), "lines."
  return data





def getAlgo ( arg = None ) :

  global onAlgo

  if arg != None :
    try :
      arg = int ( arg )
      if arg <= 0 : raise ValueError
      if arg > onFile - 1 : raise ValueError
      return arg - 1

    except ValueError:
      print '\n  Not an integer in the list'

  print '\n  Listing available algorithms\n'
  for algo in ALGO :
    print "  %-3s%-50s" % ( str ( onAlgo ) , algo )
    onAlgo = onAlgo + 1

  algoPicked = False
  picked = pickAlgo ( )
  if picked != False :
    return picked - 1
  while not algoPicked :
    picked = pickAlgo ( )
    if picked != False :
      algoPicked = True

  return picked - 1






def pickAlgo ( ) :

  wantAlgo = raw_input ( '\n  Enter an algorithm number (or QUIT to exit): ' )

  if str ( wantAlgo ).upper ( ) == 'QUIT':
    print '\n  Goodbye\n'
    sys.exit ( )

  try :
    wantAlgo = int ( wantAlgo )
    if wantAlgo <= 0 : raise ValueError

  except ValueError:
    print '\n  Not an integer in the list'
    return False

  if wantAlgo > onAlgo - 1 : 
    print '\n  Not an integer in the list'
    return False

  return wantAlgo




def prettyInterp ( interp , braces = True ) :
  output = '{ ' if braces else ''
  for assign in sorted ( interp.keys ( ) ) :
    output = output + 'p' + str ( assign ) + ' -> ' + str ( interp [ assign ] ) + ' , '
  output = output [ : -2 ] 
  if braces : output = output + '}'
  return output

def asciiArt ( ) :
  print '\n ',
  for i in xrange ( 0 , LINEWIDTH ) : print '-',
  print '\n   _____      _______        _                '
  print '  / ____|  /\|__   __|      | |               '
  print ' | (___   /  \  | |___  ___ | |_   _____ _ __ '
  print '  \___ \ / /\ \ | / __|/ _ \| \ \ / / _ \ \'__|'
  print '  ____) / ____ \| \__ \ (_) | |\ V /  __/ |   '
  print ' |_____/_/    \_\_|___/\___/|_| \_/ \___|_| \n'
  print ' ', ' , '.join ( ALGO )
  print '\n ',
  for i in xrange ( 0 , LINEWIDTH ) : print '-',
  print ''

if __name__ == "__main__" :
    main ( sys.argv [1:] )