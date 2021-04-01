#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from pgmpy.readwrite import BIFReader
from pgmpy.models import BayesianModel
import time

def get_indicator_clauses(bayes_net):
    # Get variable list, and initialize list to capture indicator clauses.
    variables = bayes_net.get_values()
    indicator_clauses = []
    
    # For every variable, create a clause joining every positive literal in the
    # variable's domain
    for var in variables:
        
        clause = False
        var_domain = len(variables.get(var))
        for x in range(var_domain):
            literal = 'lambda_' + var + "_" + str(x)
            clause = (str(clause)+"||"+str(literal))
        indicator_clauses.append(clause)
    # Create a clause of every pair of domain values as negative literals.
        for i in range(var_domain):
            for j in range(i + 1,var_domain):
                first_literal = "!lambda_" + var + "_" + str(i)
                second_literal = "!lambda_" + var + "_" + str(j)
                clause = (str(first_literal)+"||"+str(second_literal))
                indicator_clauses.append(clause)
                
    return indicator_clauses

def get_theta_parameter_clauses(bayes_net):
    # Make list to capture clauses, and initialize list of variables and parents
    parameter_clauses = []
    variables = bayes_net.get_values()
    parents = bayes_net.get_parents()
    
    # For every variable, get all possible configurations of that
    # variable's parent domains, using the configuration function.
    for var in variables:
        parent_vars = parents.get(var)
        domains = []
        for parent in parent_vars:
            parent_values = variables.get(parent)
            domain = [[i for i in range(1,len(parent_values) + 1)]]
            domains += domain
        configs = []
        if len(parent_vars) != 0:
            configurations(parent_vars, [0]*len(parent_vars), len(parent_vars), domains, configs)
    # With all possible parent domains, create clauses and add them to list.
    # Add the parameters to the parameter list.
            for config in configs:
                clause = []
                theta = "theta_" + str(var)
                for i in range(len(parent_vars)):
                    parent = parent_vars[i]
                    clause += ["lambda_" + str(parent) + "_" + str(config[i])]
                clause = "||".join(clause)
                for x in range(len(variables.get(var))):
                    theta_n = theta + "_" + str(x)
                    final_clause = clause + "<=>" + theta_n
                    parameter_clauses.append(final_clause)
    # If the variable has no parents, create a seperate theta parameter.
        else:
            for x in range(len(variables.get(var))):
                theta = "theta_" + str(var) + "_" + str(x)
                parameter_clauses.append(theta)
    return parameter_clauses
                
def configurations(parents, indices, current_depth, domains, list_of_clauses):
    
    #Before running, initialize indices to [0]*len(parents) and
    #current_depth to len(parents)

    # Helper function for theta parameter clauses. Needed to determine all
    # possible configurations of discrete domain values.

    def max_list_length(list_of_lists):
        max_list_length = 0
        for list_object in list_of_lists:
            if len(list_object) > max_list_length:
                max_list_length = len(list_object)
        return max_list_length
    
    if current_depth == 0:
        list_of_domain_values = [indices[i] for i in range(len(parents))]
        check = True
        for i in range(len(parents)):
            if list_of_domain_values[i] > len(domains[i]):
                check = False
        if check:
            list_of_clauses.append(list_of_domain_values)
        return
    
    for i in range(1,max_list_length(domains)+1):
        indices[current_depth-1] = i-1
        configurations(parents, indices, current_depth-1, domains, list_of_clauses)
        
def ENC1Encoding(bayes_net):
    
    # Bayes_net variable must be in the form of a bif file. I.e.,
    # using the function BIFReader, read in a .bif file, then output
    # the indicator and parameter clauses specified by ENC1 encoding
    
    # Still need to find a better way to encode a CNF statement. A better
    # alternative would avoid having the OR FALSE in a lot of the indicator
    # clauses. As is, the parameter_clauses function does not manage to get
    # a neat CNF statement. Also, the || operators are standing in for AND
    # statements. A better CNF package would help here. Will have to figure 
    # something out.
    start = time.time()
    indicator_clauses = get_indicator_clauses(bayes_net)
    parameter_clauses = get_theta_parameter_clauses(bayes_net)
    clauses = indicator_clauses + parameter_clauses
    end = time.time()
    print("This process took " + str(end - start) + " long. In however many seconds.")
    return clauses