# -*- coding: utf-8 -*-
"""


@author: Sahba
"""
from State import *



def Read_Input(grammar):
    file_name = "grammar3.txt"       #get file

    file = open(file_name,'r' )
    lines_list = file.readlines()

    for line in lines_list:
        line = line.strip('\n')
        line = line.replace(' ' , '')

        if line !='':
            line_list = line.split('->')   #parse the grammar

            if line_list[0].isupper():

                if '|' in line_list[1]:
                    production_list = line_list[1].split('|')

                    for prod in production_list:
                        grammar.append([line_list[0],prod])
                                              #each terminal has a list of RHS of productions
                else:
                    grammar.append(line_list)      #grammar has list of productions
            else:
                print("Error!")




def Term_Nonterm(grammar , term , non_term ):

    for production in grammar:
        if production[0] not in non_term:   #production[0]=LHS
            non_term.append( production[0] )


        for char in production[1 ]:
            if not char.isupper():

                if char not in term:
                    term.append( char )


def calculate_firstset(grammar , first , term , non_term):
                       #first=dict()
    for t in term:
        first[t] = t
    for nt in non_term:
        first[nt] = set({})  #initialize
    for nt in non_term:
        get_first(nt, grammar, first, term)



def get_first(nonterm , grammar ,first , term):  #nonterm=symbol

    for production in grammar:
        if nonterm in production[0]:
            rhs = production[1]
            first_char = rhs[0]

            #if starts with a term
            if first_char in term:
                first[nonterm].add(first[first_char])
            else:
                if not first[first_char] and   nonterm !=  first_char:  #if starts with nonterm
                    get_first(first_char,grammar,first,term)

                i = 0
                while i <len(rhs) and  'e' in first[rhs[i]]: #if it has a e derivation
                    for symbol in first[rhs[i]]:
                        if 'e' != symbol:
                            first[nonterm].add(symbol)
                    i += 1
                if i == len(rhs):
                    first[nonterm].add('e')     #they all have e derivation
                else:
                    for symbol in  first[rhs[i]]:
                        first[nonterm].add(symbol)


def Get_Augmented( grammar , augment_grammar):

    augment_grammar.append([grammar[0][0]  + "'" ,  grammar[0][0]])  #add augmented grammar
    augment_grammar.extend( grammar )  #add other rules fram original grammar


def Closure(I , augment_grammar , first,non_term):

    while True:
        added = False

        for item in I:
            dot_pos = item[1].index('.')  #item[1]=right hand side #item[0]=left hand side
            if dot_pos == (len(item[1]) - 1):  #if dot is at the end (reduce)
                continue
            next_symbol = item[1][dot_pos + 1] #next symbol after dot
            if next_symbol in non_term:   #if next symbol is nonterm
                for production in augment_grammar:  #add its productions
                    if next_symbol == production[0]:
                        if production[1] == 'e':
                            rhs = 'e.'
                        else:
                            rhs = '.' + production[1]


                        lookahead = []  # calculate look ahead
                        if dot_pos < (len(item[1]) - 2):
                            remainder = item[1][dot_pos + 2]
                            for symbol in first[remainder]:
                                if 'e' == symbol: #e derivation
                                    for elem in item[2]:  #item[2]=lookahead
                                        if elem not in lookahead:
                                            lookahead.append(elem)
                                else:
                                    if symbol not in lookahead:
                                        lookahead.append(symbol)

                        else:
                            lookahead = deepcopy(item[2])

                        newitem = [next_symbol, rhs, lookahead]  # structure of each item

                        if newitem not in I:
                            same_core = False
                            for item_ in I:
                                if item_[0] == newitem[0] and item_[1] == newitem[1]:
                                    same_core = True
                                    for la in lookahead:
                                        if la not in item_[2]:
                                            item_[2].append(la)
                                            added = True

                            if not same_core:
                                I.append(newitem)
                                added = True

        if not added:
            break


def Goto(I,symbol , augment_grammar,first,non_term):

    J = []

    for item in I:
        dot_pos = item[1].index('.')

        if dot_pos < len(item[1]) - 1: #dot is somewhere in the middle
            next_char = item[1][dot_pos + 1]
            if next_char == symbol:  # if symbol is the symbol after dot

                new_rhs = item[1].replace('.' + symbol, symbol + '.')
                new_item = [item[0], new_rhs, item[2]]  #new item made by goto action
                J.append(new_item)

    Closure(J, augment_grammar, first, non_term)

    return J


def isSame(states,newstate,I,Symbol): #checks if new state was made before

    for J in states:
        if J.state == newstate:
            I.update_goto(  Symbol ,J )
            return True

    return False


def init_FirstState(augment_grammar,first,non_term):  #first state

    I0 = [[augment_grammar[0][0], '.' + augment_grammar[0][1], ['$']]]   #first state: startsymbol,.RHS
    Closure(I0, augment_grammar,first,non_term)

    return I0


def Add_States(states , augment_grammar , first , term , non_term):

    first_state = init_FirstState(augment_grammar, first, non_term)

    states.append( State(first_state))
    all_symb = non_term + term

    while True:

        added = False
        for I in states:
            for symbol in all_symb:
                new_state = Goto(I.state, symbol, augment_grammar, first, non_term)  # goto(I,symbol)
                if (new_state != []) and not isSame(states, new_state, I, symbol): #if new state is not empty and it is not repeated
                    s =State(new_state)
                    I.update_goto(symbol, s)
                    s.update_parentName(I, symbol)
                    states.append(s)
                    added = True

        if not added:
            break



def get_parse_table(parse_table , states , augmented_grammar):


    for index, I in enumerate(states):
        parse_table.append(I.actions)

        for item in I.state:
            rhs_list = item[1].split('.')
            if rhs_list[1] == '': #is reduce
                prod_no = augmented_grammar.index([item[0], rhs_list[0]])

                for la in item[2]:

                    parse_table[index][la] = -prod_no




def parse(parse_table, augment_grammar, inpt):
    inpt = list(inpt + '$')
    stack = [0]
    inp = inpt[0]
    try:
        while True:

            s = stack[len(stack) - 1]
            action = parse_table[s][inp]
            if action > 0:
                inpt.pop(0)
                stack.append(action)
                print('Shifting :', inp)
                inp = inpt[0]
            elif action < 0:
                prod = augment_grammar[-action]
                if prod[1] != 'e':
                    for i in range(len(prod[1])):
                        stack.pop()
                t = stack[len(stack) - 1]
                stack.append(parse_table[t][prod[0]])
                print('Reducing :', prod[0]+'->'+ prod[1])
            elif action == 0:
                print('ACCEPT')
                break
    except :
        print('ERROR')


def Print_States(grammar, augment_grammar, term, non_term, first, states):




    print('\n\nLR(1) States: ')
    for state in states:
        print("\n goto", state.parent,'=', state.state_num)
        for item in state.state:
            print(item)
        if state.actions != {}:
           print('Actions : ')

        for key, value in state.actions.items():
            print(key, '->', value)



g=[]
terms=[]
nonterms=[]
f=dict()
a=[]
s=[]

p_t=[]

Read_Input(g)

Term_Nonterm(g,terms,nonterms)  #print nonterms and terms
print('\nterms:',terms, '\nnon terms:',   nonterms)


calculate_firstset(g,f,terms,nonterms) #print firstset for nonterms

print('\nfirstsets:')
for nont in nonterms:
    print(nont, '->', f[nont])

Get_Augmented(g,a) #print augmented grammar

print('\naugment grammar:')
for production in g:
    print(production[0],'->',production[1])


Add_States(s,a,f,terms,nonterms)

#print(s)

get_parse_table(p_t,s,a)
#print((p_t))

parse(p_t,a,"i+n")
Print_States(g, a, terms, nonterms, f, s)