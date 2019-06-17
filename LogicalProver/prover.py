# -*- coding: utf-8 -*-
"""
Created on Mon Nov 20 23:11:38 2017

@author: Utilizador
"""

import sys

class MyLiteral:
    def __init__(self,Name=[],LogValue=[]):
        self.Name=Name
        self.LogValue=LogValue
    
    def __repr__(self):
        return '{}:{}'.format(self.Name, self.LogValue)
    def __eq__(self, other):
        return self.Name==other.Name and self.LogValue==other.LogValue
        
def read_sentence(line):
    
    cl=[]

    not_test='not'
    line_len=len(line)
    
    if (line_len>1): # 1 literal negated or more than 1 literal
        if line[0]==not_test: # 1 literal negated
            newLit1=MyLiteral(Name=line[1],LogValue=False)
            cl.append(newLit1)
        else: # more than 1 literal
            for i in range(0, line_len):
                if not_test in line[i][0]:
                    newLit1=MyLiteral(Name=line[i][1],LogValue=False)
                    cl.append(newLit1)
                else:
                    newLit1=MyLiteral(Name=line[i][0],LogValue=True)
                    cl.append(newLit1)

    else: # 1 literal not negated
        newLit1=MyLiteral(Name=line[0],LogValue=True)   
        cl.append(newLit1)         
 
    return cl

#Applies Simplification 1: remove a clause C if it contains a literal that is not complementary with any other in the remaining clauses
def simplif1(cl_list):
    
    confirmed_lit=[]
    flag=-1
    num_cl=len(cl_list)
    if num_cl==1:
        cl_list=[]
        return cl_list
    for i in range(num_cl):
        for literal in cl_list[i]:
            flag=-1
            if literal.Name in confirmed_lit:  
                continue
            for k in range(i+1, num_cl):
                for lit_aux in cl_list[k]:
                    if lit_aux.Name==literal.Name and literal.LogValue!= lit_aux.LogValue:
                        flag=1
                        break
                if flag==1:
                    break
            if flag==1:
                confirmed_lit.append(literal.Name)
                continue
            if flag==-1:
                for cl_remove in cl_list:
                    for lit_remove in cl_remove:
                        if lit_remove.Name==literal.Name:
                            cl_list.remove(cl_remove)
                            break	
                return cl_list
    return False

#Applies Simplification 2: remove tautologies
def simplif2(cl_list):

    num_cl=len(cl_list)
    cl_remove_list=[]

    for i in range(0,num_cl):
        flag=0
        for lit in cl_list[i]:
            for lit_aux in cl_list[i]:
                if lit_aux.Name==lit.Name and lit.LogValue!= lit_aux.LogValue:
                    cl_remove_list.append(cl_list[i])
                    flag=1
                    break
            if flag==1:
                break

    for cl in cl_remove_list:
        cl_list.remove(cl)

    return cl_list
            
#Applies Simplification 3: remove equal clauses
def simplif3(cl_list):
    for cl in cl_list:
        flag=0
        for cl2 in cl_list:
            if cl==cl2:
                flag=flag+1
            else:
                continue
        if flag>1:
            cl_list.remove(cl)
    return cl_list
            
def resolution(first_cl,second_cl,literal,result_list):
    new_cl=[]
    for lit_aux in second_cl:
        if lit_aux.Name==literal.Name and literal.LogValue!= lit_aux.LogValue:
            for lit1 in first_cl:
                if lit1.Name!=literal.Name:
                    new_cl.append(lit1)
            for lit2 in second_cl:
                if lit2.Name!=literal.Name:
                    new_cl.append(lit2)
            if new_cl not in result_list:
                result_list.append(new_cl)
                return True
        else:
            continue
    return False    

def prover(cl_list):
   # print(prov)
    prov=None
    cl_list = sorted(cl_list, key= lambda x: len(x))  #ordena a lista por tamanho das clauses
    if cl_list=={}:
        prov=False
        return cl_list,prov
    if cl_list[0]==[]:
        prov=True
        return cl_list,prov
    num_cl=len(cl_list)
    for i in range(num_cl):
        if i==(num_cl-1):
            prov=False
            return cl_list,prov
        first_cl=cl_list[i]
        for lit in first_cl:
            for k in range(i+1,num_cl):
                second_cl=cl_list[k]
                cl_list_new=cl_list
                if resolution(first_cl,second_cl,lit,cl_list_new)==False:
                    continue
                else:
 
                    simplif2(cl_list_new)
                    simplif1(cl_list_new)
 
                    simplif3(cl_list_new)
                    cl_list_new = sorted(cl_list_new, key= lambda x: len(x))  #ordena a lista por tamanho das clauses
                    if cl_list_new!=cl_list:
                        return cl_list_new,None                  
                    else:
                        continue

if __name__=="__main__":
    cl_list=[]
    received = []
    cl_list_new=[]
    simplium=None
    for line in sys.stdin:
       	received=read_sentence(eval(line))
        cl_list.append(received)
    #print("lista recebida:",cl_list)
    simplium=simplif1(cl_list)
    while simplium!=False:
        simplium=simplif1(cl_list)
    simplif2(cl_list)  
    simplif3(cl_list)
    prov=None
    while True:
        #print(cl_list) atualização da lista a cada vez que se aplica a resolução
        cl_list, prov =prover(cl_list)
        if prov!=None:
            break
        

    print(prov)
