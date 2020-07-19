### ---------------------------------------------- ###
# This file generates all non-empty combinations of 
# Boolean connectives and outputs a CSV file that pairs them 
# with the informativeness and complexity values
### ---------------------------------------------- ###

from __future__ import division

"""
LANGUAGE MODEL
"""
	
# Define the powerset function that generates all the subsets of a set. 
def powerset(seq):
    if len(seq) <= 1:
        yield seq
        yield []
    else:
        for item in powerset(seq[1:]):
            yield [seq[0]]+item
            yield item

# Define a subset function (from two lists to a truth value).
def subset(sub,sup):
	if(all(x in sup for x in sub)): 
		return True
	else:
		return False

# The list of all possible connectives
connective = [[1,1,1,1],[1,1,1,0],[1,1,0,1],[1,1,0,0],[1,0,1,1],[1,0,1,0],[1,0,0,1],[1,0,0,0],[0,1,1,1],[0,1,1,0],[0,1,0,1],[0,1,0,0],[0,0,1,1],[0,0,1,0],[0,0,0,1],[0,0,0,0]]

# Generate the set of languages
langs = powerset(connective)
langs = list(langs)
langs.remove([]) # remove the empty language

"""
MODELLING SCALAR IMPLICATURE
"""

# A function returning the set of innocently excludable alternatives given a prejacent word and the language (set of words)
def ie_fun(prej,lang):
	# first we take the alts that are non-weaker 
	alts = []
	for alt in lang:
		zipobj = zip(prej,alt)
		if any(prej_i > alt_i for prej_i, alt_i in zipobj): # If the alt is non-weaker than the prej, 
			alts = alts + [alt] # add the alt to the set of alts
	if alts == []:
		return []

	# From the given set of alternatives, we derive all the possible subsets (powerset) minus the empty set. 
	power = list(powerset(alts))
	power.remove([])

	ieset = []
	for altset in power:
		negaltsets = map(lambda x: map(lambda y: int(not(y)),x),altset)  # This inverts the truth values of words in altset
	# print altset, negaltsets  
		withprej = negaltsets + [prej]   # combines the negated altset with the prejacent
	# print withprej
		if any(all(w[i] == 1 for w in withprej) for i in range(4)): # if withprej is consistent (i.e., if it contains any 1 across all words)
			if ieset == []:               # in the beginning, just add the altset currently considering to the ieset
				ieset = [altset]
			else:                         # from the second time and on, we have to consider the maximality of the altset
				for s in ieset:
					if subset(s,altset):   # if a member of ieset is already a subset of altset currently considering
						i = ieset.index(s)  # retrieve the index of the subset already in ieset
						del ieset[i]        # remove the subset from ieset
						ieset = ieset + [altset] # update the ieset with the altset currently considering
					elif not(any(subset(altset,s) for s in ieset)): # Otherwise, and if there is no member of ieset that is a superset of altset under consideration
						ieset = ieset + [altset] # update the ieset with the altset currently considering				
	if ieset == []:
		return []

	# get the intersection of ieset
	ie = []
	for alt in ieset[0]:
		if all(alt in ieset[i] for i in range(1,len(ieset))):
			ie = ie + [alt]

	return ie

# Function that returns the strengthened meaning of a prejacent word given the prejacent word and the language
def si(prej,lang):
	ie = ie_fun(prej,lang)
	if ie == []:
		return prej
	negie = map(lambda x: map(lambda y: int(not(y)),x),ie)
	combined = negie + [prej]
	strengthened = [0]*4
	for i in range(4):
		if all(w[i]==1 for w in combined):
			strengthened[i] = 1
		# else:
		# 	strengthened[i] = 0
	return strengthened

# Function that returns the strengthened representation of a language by strengthening each word in it
def strengthen(lang):
	# new_lang = []
	new_lang = [[]]*len(lang)
	for i in range(len(lang)):
		si_word = si(lang[i],lang)
		new_lang[i] = si_word
	return new_lang

"""
MODELLING INFORMATIVENESS
"""

# Define several utility functions
def utility(world1,world2):
	if world1 == world2:
		return 1
	elif (world1 == 0 and world2 == 3) or (world1 == 3 and world2 == 0):
		return 1/3
	else:
		return 1/2

def utility2(world1,world2):
	if world1 == world2:
		return 1
	else:
		return 0

def utility3(world1,world2):
	if world1 == world2:
		return 1
	elif (world1 == 0 and world2 == 3) or (world1 == 3 and world2 == 0):
		return 0
	else:
		return 1/2

# Function that returns the informativeness value of a language

def info(lang):
	info = 0
	for world in range(4):
		truewords = list(filter(lambda x: x[world] == 1, lang))
		for word in truewords:
			for world2 in range(4):
				if word[world2] == 1:
					info = info + 1/len(truewords)*1/sum(word)*utility3(world,world2)
			# print 1/len(truewords)
	return info

"""
MODELLING COMPLEXITY
"""

# assign complexity to each connective: 
## This counts the number of connectives appearing the formula in Propositional Logic containing \wedge, \vee and \neg which must contain both p and q. 
connective_values1 = {
	repr([1,1,1,0]): 1,
	repr([1,0,0,0]): 1,
	repr([1,1,0,1]): 2,
	repr([1,0,1,1]): 2, 
	repr([0,1,1,1]): 2,
	repr([0,1,0,0]): 2,
	repr([0,0,1,0]): 2,
	repr([0,0,0,1]): 2,
	repr([1,1,0,0]): 3,
	repr([1,0,1,0]): 3,
	repr([0,0,0,0]): 3,
	repr([1,1,1,1]): 4,
	repr([1,0,0,1]): 4,
	repr([0,1,1,0]): 4,
	repr([0,1,0,1]): 4,
	repr([0,0,1,1]): 4
}

## This counts the number of connectives+literals appearing the formula in Propositional Logic containing \wedge, \vee and \neg (which don't have to contain both p and q). 
connective_values2 = {
	repr([1,1,1,0]): 3,
	repr([1,0,0,0]): 3,
	repr([1,1,0,1]): 4,
	repr([1,0,1,1]): 4, 
	repr([0,1,1,1]): 4,
	repr([0,1,0,0]): 4,
	repr([0,0,1,0]): 4,
	repr([0,0,0,1]): 4,
	repr([1,1,0,0]): 1,
	repr([1,0,1,0]): 1,
	repr([0,0,0,0]): 4,
	repr([1,1,1,1]): 4,
	repr([1,0,0,1]): 8,
	repr([0,1,1,0]): 8,
	repr([0,1,0,1]): 2,
	repr([0,0,1,1]): 2
}

## This counts the number of connectives (but not literals) appearing the formula in Propositional Logic containing \wedge, \vee and \neg (which don't have to contain both p and q). 
connective_values3 = {
	repr([1,1,1,0]): 1,
	repr([1,0,0,0]): 1,
	repr([1,1,0,1]): 2,
	repr([1,0,1,1]): 2, 
	repr([0,1,1,1]): 2,
	repr([0,1,0,0]): 2,
	repr([0,0,1,0]): 2,
	repr([0,0,0,1]): 2,
	repr([1,1,0,0]): 0,
	repr([1,0,1,0]): 0,
	repr([0,0,0,0]): 2,
	repr([1,1,1,1]): 2,
	repr([1,0,0,1]): 4,
	repr([0,1,1,0]): 4,
	repr([0,1,0,1]): 1,
	repr([0,0,1,1]): 1
}

## Same as above but with additional weight (+1) for negation
## This counts the number of connectives (but not literals) appearing the formula in Propositional Logic containing \wedge, \vee and \neg (which don't have to contain both p and q). 
connective_values4 = {
	repr([1,1,1,0]): 1,
	repr([1,0,0,0]): 1,
	repr([1,1,0,1]): 3,
	repr([1,0,1,1]): 3, 
	repr([0,1,1,1]): 3,
	repr([0,1,0,0]): 3,
	repr([0,0,1,0]): 3,
	repr([0,0,0,1]): 3,
	repr([1,1,0,0]): 0,
	repr([1,0,1,0]): 0,
	repr([0,0,0,0]): 3,
	repr([1,1,1,1]): 3,
	repr([1,0,0,1]): 5,
	repr([0,1,1,0]): 5,
	repr([0,1,0,1]): 2,
	repr([0,0,1,1]): 2
}

## define a function that calculates complexity
def comp(lang,lot):
	comp = 0
	for word in lang:
		comp = comp + lot[repr(word)]
	return comp

"""
GENERATING THE TABLE
"""

# Generate the table pairing each language with its complexity and informativeness
for lang in langs:
	print '"',lang, '",', comp(lang,connective_values2), ',', info(strengthen(lang))

