### ----------------------------------------------------------- 
# This file generates all non-empty combinations of 
# Boolean connectives and outputs the following two CSV files
# - "full.csv": CSV file that pairs each language with the complexity and informativeness values
# - "pareto.csv": CSV file that pairs each Pareto-optimal language with the complexity and informativeness values
# It also generates the plot of all inventories based on the complexity and informativeness values
# REQUIRES python3
### -----------------------------------------------------------
# Updated 23/07/20: Added a function that automatically computes 
# the Pareto-optimal frontier, thanks to Moysh Bar-Lev. 

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

# The list of all commutative connectives
# connective=[[1,1,1,1],[1,1,1,0],[1,0,0,1],[1,0,0,0],[0,1,1,1],[0,1,1,0],[0,0,0,1],[0,0,0,0]]

# The list of all commutative non-tautological connectives
#connective=[[1,1,1,0],[1,0,0,1],[1,0,0,0],[0,1,1,1],[0,1,1,0],[0,0,0,1],[0,0,0,0]]

# The list of four-corner connectives
#connective = [[1,0,0,0],[1,1,1,0],[0,1,1,1],[0,0,0,1]]


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
		negaltsets = list(map(lambda x: list(map(lambda y: int(not(y)),x)),altset))  # This inverts the truth values of words in altset
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
	negie = list(map(lambda x: list(map(lambda y: int(not(y)),x)),ie))
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
					info = info + 1/4*1/len(truewords)*1/sum(word)*utility2(world,world2)
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


connective_names={
	"TAU": [1,1,1,1],
	"<-": [1,1,0,1],
	"P": [1,1,0,0],
	"->": [1,0,1,1],
	"Q": [1,0,1,0],
	"<->": [1,0,0,1],
	"NAND": [0,1,1,1],
	"XOR": [0,1,1,0],
	"NOTQ": [0,1,0,1],
	"ONLYP": [0,1,0,0],
	"NOTP": [0,0,1,1],
	"ONLYQ": [0,0,1,0],
	"NOR": [0,0,0,1],
	"CONT": [0,0,0,0],
	"OR": [1,1,1,0],
	"AND": [1,0,0,0],
	"NOR": [0,0,0,1],
	"NAND": [0,1,1,1]	
}

def name(word):
	for x in connective_names:
		if word==connective_names[x]:
			wordname=x
	return wordname
	
def names(lang):
	langnames=[]
	for word in lang:
		langnames=langnames + [name(word)]
	return langnames


# Generate the table pairing each language with its complexity and informativeness
#for lang in langs:

table=[]
for lang in langs:
	table.append([lang,comp(lang,connective_values2),info(strengthen(lang)),names(lang)])
#	print (table)

import csv

with open('full.csv', mode='w', newline='') as temp:
	temp_writer = csv.writer(temp)
	for i in table:
		temp_writer.writerow(i)

"""
Computing pareto frontier
"""

table_negcomp=[]
for i in table:
	table_negcomp.append([-i[1],i[2]])

import numpy as np
import matplotlib.pyplot as plt

efficient = np.array(table_negcomp)
#print(efficient)

x = efficient[:, 0]
y = efficient[:, 1]

plt.scatter(x, y)
plt.xlabel('Complexity')
plt.ylabel('Informativeness')
plt.show()

def identify_pareto(efficient):
    # Count number of items
    population_size = efficient.shape[0]
    # Create a NumPy index for scores on the pareto front (zero indexed)
    population_ids = np.arange(population_size)
    # Create a starting list of items on the Pareto front
    # All items start off as being labelled as on the Parteo front
    pareto_front = np.ones(population_size, dtype=bool)
    # Loop through each item. This will then be compared with all other items
    for i in range(population_size):
        # Loop through all other items
        for j in range(population_size):
            # Check if our 'i' pint is dominated by out 'j' point
            if all(efficient[j] >= efficient[i]) and any(efficient[j] > efficient[i]):
                # j dominates i. Label 'i' point as not on Pareto front
                pareto_front[i] = 0
                # Stop further comparisons with 'i' (no more comparisons needed)
                break
    # Return ids of scenarios on pareto front
    return population_ids[pareto_front]

pareto = identify_pareto(efficient)

pareto_front = efficient[pareto]

pareto_front_plus=[]
for i in pareto:
	pareto_front_plus.append(table[i])
print("Connectives:", names(connective))
print("Pareto front:", pareto_front_plus)

with open('pareto.csv', mode='w', newline='') as temp:
	temp_writer = csv.writer(temp)
	for i in pareto_front_plus:
		temp_writer.writerow(i)