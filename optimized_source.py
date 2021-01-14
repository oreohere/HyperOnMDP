import itertools
import time

import stormpy
from lark import Lark, Token
from z3 import *

import files

turtle_grammar = """
    start:  "AS" NAME "." start -> forall_scheduler
          | "ES" NAME "." start -> exist_scheduler
          | "A" NAME "." start -> forall
          | "E" NAME "." start -> exist
          | varname  -> var
          | "(" start "&" start ")"-> and_op
          | "(" start "|" start ")"-> or_op
          | "~" start -> neg_op
          | "true" -> true
          | "(" p "<" p ")" -> less_prob
          | "(" p "=" p ")" -> equal_prob
          | "(" p ">" p ")" -> greater_prob
          | "(" p ">=" p ")" -> greatereq_prob
          | "(" p "<=" p ")" -> lesseq_prob

    p: "P" phi  -> calc_probability
          |p "+" p -> add_prob
          | p "-" p -> minus_prob
          | p "." p -> mul_prob
          | NUM -> const

    phi:  "(X" start ")" -> calc_next
          | "(" start "U" start ")"-> calc_until_unbounded
          | "(" start "U["NUM "," NUM"]" start ")"-> calc_until_bounded
          | "(F" start ")" -> calc_future
    ap: "f"
          |"t"
          | varname
          | varname "&" ap  ->and_vars
          |"(" varname "|" varname ")" ->or_vars
          |ap "=>" start ->imply_vars
          |ap "<->" ap ->iff_vars
    varname: NAME "(" NAME ")" ->varname


    %import common.CNAME -> NAME
    %import common.NUMBER ->NUM
    %import common.WS_INLINE
    %ignore WS_INLINE
"""
parser = None
list_of_subformula = []
list_of_reals = []
listOfReals = []
list_of_bools = []
listOfBools = []
list_of_ints = []
listOfInts = []
s = None
nos_of_subformula = 0
f_pointer = None


def SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n):
    print("Starting until")
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    phi2 = formula_duplicate.children[0].children[1]
    index_of_phi2 = list_of_subformula.index(phi2)
    result_string = 'A(' + Semantics(model, phi1, combined_list_of_states, n) + ' ' + Semantics(model, phi2,
                                                                                                combined_list_of_states,
                                                                                                n) + ')'
    index_of_phi = list_of_subformula.index(formula_duplicate)
    dict_of_acts = dict()
    dict_of_acts_tran = dict()
    for state in model.states:
        list_of_act = []
        for action in state.actions:
            list_of_tran = []
            list_of_act.append(action.id)
            for tran in action.transitions:
                list_of_tran.append(str(tran.column) + ' ' + str(tran.value()))
            dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
        dict_of_acts[state.id] = list_of_act

    for li in combined_list_of_states:
        result_string = 'A(' + result_string + ' '
        first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(
            li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
        if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
            list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
        second_implies = 'I(A(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ') N(holds_' + str(
            li[0]) + '_' + str(li[1]) + '_' + str(
            index_of_phi2) + ')) ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=0)'
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
        new_prob_const = 'G(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' 0)'
        result_string += first_implies + ' ' + second_implies + ' ' + new_prob_const + ')'
        combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
        for ca in combined_acts:
            implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ') A(a_' + str(li[0]) + '=' + str(ca[0]) + ' a_' + str(li[1]) + '=' + str(ca[1]) + '))'
            if 'a_' + str(li[0]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[0]))
            if 'a_' + str(li[1]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[1]))

            implies_antecedent_and1 = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
            combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                   dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
            first = False
            if len(combined_succ) == 1:
                first = True
            prod_left = 'P('
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                if first:
                    prod_left = 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + \
                                cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi) + ') '
                else:
                    prod_left += 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + \
                                 cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi) + ') '
                if 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi) not in list_of_z3_variables:
                    list_of_z3_variables.append(
                        'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi))
            if first:
                implies_antecedent_and1 += prod_left[0:len(prod_left) - 1] + ')'
            else:
                implies_antecedent_and1 += prod_left[0:len(prod_left) - 1] + '))'
            implies_antecedent_and2 = 'I(g(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' 0) '
            prod_right_or = 'V('
            first = False
            if len(combined_succ) == 1:
                first = True
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                if first:
                    prod_right_or = 'V(holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) + ' g(d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                        index_of_phi2) + ' d_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) + ')) '
                else:
                    prod_right_or += 'V(holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) + ' g(d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                        index_of_phi2) + ' d_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) + ')) '
                if 'holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append(
                        'holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2))
                if 'd_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append('d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
                if 'd_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append(
                        'd_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2))
            if first:
                implies_antecedent_and2 += prod_right_or[0:len(prod_right_or) - 1] + ')'
            else:
                implies_antecedent_and2 += prod_right_or[0:len(prod_right_or) - 1] + '))'
            implies_antecedent = 'A(' + implies_antecedent_and1 + ' ' + implies_antecedent_and2 + ')'
            result_string = 'A(' + result_string + ' I(' + implies_precedent + ' ' + implies_antecedent + '))'
    print("Done with until")
    return result_string


def SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n):
    result_string = ''
    phi1 = formula_duplicate.children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    phi2 = formula_duplicate.children[3]
    index_of_phi2 = list_of_subformula.index(phi2)
    k1 = int(formula_duplicate.children[1].value)
    k2 = int(formula_duplicate.children[2].value)
    index_of_phi = list_of_subformula.index(formula_duplicate)
    if k2 == 0:
        result_string = 'A(' + Semantics(model, phi1, combined_list_of_states, n) + ' ' + Semantics(model, phi2,
                                                                                                    combined_list_of_states,
                                                                                                    n) + ')'
        result_string = 'A(' + result_string + ' '
        sum_of_loop1 = 'A('
        sum_of_loop2 = 'A('
        for li in combined_list_of_states:
            first_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '=1' + ' holds_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ')'
            second_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + '=0' + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + '))'
            final_or1 = 'V(' + first_and1 + ' ' + second_and1 + ')'
            sum_of_loop1 += final_or1 + ' '
            first_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '=1' + ' holds_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ')'
            second_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + '=0' + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + '))'
            final_or2 = 'V(' + first_and2 + ' ' + second_and2 + ')'
            sum_of_loop2 += final_or2 + ' '
            if "prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append("prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            if "prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append("prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
        sum_of_loop1 = sum_of_loop1[0:len(sum_of_loop1) - 1] + ')'
        sum_of_loop2 = sum_of_loop2[0:len(sum_of_loop2) - 1] + ')'
        result_string += sum_of_loop1 + ')'
        result_string = 'A(' + result_string + ' ' + sum_of_loop2 + ')'

        for li in combined_list_of_states:
            result_string = 'A(' + result_string + ' '
            first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                list_of_z3_variables.append(
                    'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
            second_implies = 'I(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ')' + ' prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi) + '=0)'
            result_string += first_implies + ' ' + second_implies + ')'
        result_string += ')'

    elif k1 == 0:
        left, k_1, k_2, right = formula_duplicate.children
        par = copy.deepcopy(k_2)
        par.value = str(
            int(
                k_2.value) - 1)  # k2.value will have changed value but it won't show up in the formula tree, hence it'll appear to be the same formula as formula_duplicate
        formula_duplicate.children[
            2] = par  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2. Don't be confused!!
        list_of_subformula.append(formula_duplicate)
        index_of_replaced = len(
            list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
        result_string = SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)

        dict_of_acts = dict()
        dict_of_acts_tran = dict()
        for state in model.states:
            list_of_act = []
            for action in state.actions:
                list_of_tran = []
                list_of_act.append(action.id)
                for tran in action.transitions:
                    # list_of_tran.append({tran.column: tran.value()})
                    list_of_tran.append(tran.value())
                dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
            dict_of_acts[state.id] = list_of_act

        for li in combined_list_of_states:
            result_string = 'A(' + result_string + ' '
            first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
            second_implies = 'I(A(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + ') N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ')) ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=0)'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            result_string += first_implies + ' ' + second_implies + ')'
            combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
            for ca in combined_acts:
                implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_of_phi1) + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_of_phi2) + ') A(a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) + '=' + str(
                    ca[0]) + ' a_s' + str(
                    combined_list_of_states.index(li)) + '_' + str(1) + '=' + str(ca[1]) + '))'
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(0))
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(1))

                implies_antecedent = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
                combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                       dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
                if len(combined_succ) == 1:
                    first = True
                prod = 'P('
                for cs in combined_succ:
                    if first:
                        prod = 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(
                            combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    else:
                        prod += 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(
                            combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    if 'prob_s' + str(combined_succ.index(cs)) + '_' + str(
                            index_of_replaced) not in list_of_z3_variables:
                        list_of_z3_variables.append(
                            'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced))
                if first:
                    implies_antecedent += prod[0:len(prod) - 1]
                    first = False
                else:
                    implies_antecedent += prod[0:len(prod) - 1] + ')'
                result_string = 'A(' + result_string + ' I(' + implies_precedent + ' ' + implies_antecedent + ')))'

    elif k1 > 0:
        left, k_1, k_2, right = formula_duplicate.children
        par1 = copy.deepcopy(k_1)
        par2 = copy.deepcopy(k_2)
        par1.value = str(int(k_1.value) - 1)
        par2.value = str(int(k_2.value) - 1)
        formula_duplicate.children[
            1] = par1  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2 Don't be confused!!
        formula_duplicate.children[2] = par2
        list_of_subformula.append(formula_duplicate)
        index_of_replaced = len(
            list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
        result_string = SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)

        dict_of_acts = dict()
        dict_of_acts_tran = dict()
        for state in model.states:
            list_of_act = []
            for action in state.actions:
                list_of_tran = []
                list_of_act.append(action.id)
                for tran in action.transitions:
                    # list_of_tran.append({tran.column: tran.value()})
                    list_of_tran.append(tran.value())
                dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
            dict_of_acts[state.id] = list_of_act

        for li in combined_list_of_states:
            result_string = 'A(' + result_string + ' '
            first_implies = 'I(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + ') ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi) + '=0)'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
            result_string += first_implies + ')'
            combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
            for ca in combined_acts:
                implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_of_phi1) + ' A(a_s' + str(combined_list_of_states.index(li)) + '_' + str(
                    0) + '=' + str(ca[0]) + ' a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) + '=' + str(
                    ca[1]) + '))'
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(0))
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(1))

                implies_antecedent = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
                combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                       dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
                if len(combined_succ) == 1:
                    first = True
                prod = 'P('
                for cs in combined_succ:
                    if first:
                        prod = 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(
                            combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    else:
                        prod += 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(
                            combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    if 'prob_s' + str(combined_succ.index(cs)) + '_' + str(
                            index_of_replaced) not in list_of_z3_variables:
                        list_of_z3_variables.append(
                            'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced))
                if first:
                    implies_antecedent += prod[0:len(prod) - 1]
                    first = False
                else:
                    implies_antecedent += prod[0:len(prod) - 1] + ')'
                implies_antecedent += ')'

                result_string = 'A(' + result_string + ' I(' + implies_precedent + ' ' + implies_antecedent + '))'

    return result_string


def SemanticsNext(model, formula_duplicate, combined_list_of_states, n):
    phi1 = formula_duplicate.children[0].children[0]
    Semantics(model, phi1, combined_list_of_states, n)
    index_phi1 = list_of_subformula.index(phi1)
    for li in combined_list_of_states:
        pos_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '=1 holds_' + str(
            li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ')'
        if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
        neg_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '=0 N(holds_' + str(
            li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '))'
        result_string += 'V(' + pos_and + ' ' + neg_and + ') '
    result_string = result_string[0:len(result_string) - 1] + '))'
    dict_of_acts = dict()
    dict_of_acts_tran = dict()
    for state in model.states:
        list_of_act = []
        for action in state.actions:
            list_of_tran = []
            list_of_act.append(action.id)
            for tran in action.transitions:
                list_of_tran.append(str(tran.column) + ' ' + str(
                    tran.value()))  # storing just transition values, not state it transitions to
            dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
        dict_of_acts[state.id] = list_of_act
    result_string = 'A(' + result_string + ' '
    for li in combined_list_of_states:
        combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
        for ca in combined_acts:
            implies_precedent = 'A(a_' + str(li[0]) + '=' + str(ca[0]) + ' a_' + str(li[1]) + '=' + str(ca[1]) + ')'
            if 'a_' + str(li[0]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[0]))
            if 'a_' + str(li[1]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[1]))
            mul_clause = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                list_of_subformula.index(formula_duplicate)) + ' '
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                list_of_z3_variables.append(
                    'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
            combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                   dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))

            if len(combined_succ) == 1:
                first = True
            prod = 'P('
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                if first:
                    prod = 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[0][
                                                                                                                  0:space_in0] + '_' + \
                           cs[1][0:space_in1] + '_' + str(
                        index_phi1) + ') '
                else:
                    prod += 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[
                                                                                                                       0][
                                                                                                                   0:space_in0] + '_' + \
                            cs[1][0:space_in1] + '_' + str(
                        index_phi1) + ') '
                if 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_phi1) not in list_of_z3_variables:
                    list_of_z3_variables.append(
                        'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_phi1))
            if first:
                mul_clause += prod[0:len(prod) - 1] + ')'
                first = False
            else:
                mul_clause += prod[0:len(prod) - 1] + '))'
            # implies_antecedent = '(' + mul_clause + ')'
            implies_antecedent = mul_clause
            state_act_clause = 'I(' + implies_precedent + ' ' + implies_antecedent + ')'
            result_string += state_act_clause + ' '
    result_string = result_string[0:len(result_string) - 1] + ')'
    return result_string


# most probably we can get rid of the whole combined_list_of_states

def SemanticsFuture(model, formula_duplicate, n):
    global nos_of_subformula
    print("Starting future")
    rel_quant = []
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    index_of_phi = list_of_subformula.index(formula_duplicate)
    rel_quant.extend(Semantics(model, phi1, n))
    r_state = [0 for ind in range(n)]

    dict_of_acts = dict()
    dict_of_acts_tran = dict()
    for state in model.states:
        list_of_act = []
        for action in state.actions:
            list_of_tran = []
            list_of_act.append(action.id)
            for tran in action.transitions:
                list_of_tran.append(str(tran.column) + ' ' + str(tran.value()))
            dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
        dict_of_acts[state.id] = list_of_act

    print("In future , starting line 4 of algo")
    f_pointer.write("Future :\n")

    # implement the extra logic here instead of the one below, then check for actions of that state and do the
    # actions thing          n = no.of quantifier, k = no. of state in the model
    index = []
    for j in range(0, n):
        index.append(0)
    i = n - 1
    flag = False
    while i >= 0:
        holds1 = 'holds'
        str_r_state = ""
        for ind in r_state:
            str_r_state += "_" + str(ind)
        holds1 += str_r_state + "_" + str(index_of_phi1)
        add_to_variable_list(holds1)
        prob_phi = 'prob'
        prob_phi += str_r_state + '_' + str(index_of_phi)
        add_to_variable_list(prob_phi)
        # new_prob_const = And(listOfReals[list_of_reals.index(prob_phi)] < float(1), listOfReals[list_of_reals.index(prob_phi)] >= float(0))
        new_prob_const = listOfReals[list_of_reals.index(prob_phi)] >= float(0)
        # nos_of_subformula += 1
        # s.add(new_prob_const)
        # # nos_of_subformula += 1
        # f_pointer.write(str(new_prob_const))
        # f_pointer.write("\n")
        first_implies = And(Implies(listOfBools[list_of_bools.index(holds1)],
                                    (listOfReals[list_of_reals.index(prob_phi)] == float(1))), new_prob_const)
        nos_of_subformula += 1
        # s.add(first_implies)
        # new_prob_const = Implies(Not(listOfBools[list_of_bools.index(holds1)]),

        # f_pointer.write("\n")
        dicts = []
        # rel_quant = [1,2]
        for l in rel_quant:
            dicts.append(dict_of_acts[r_state[l - 1]])
        combined_acts = list(itertools.product(*dicts))

        for ca in combined_acts:
            name = 'a_' + str(r_state[rel_quant[0] - 1])
            add_to_variable_list(name)
            act_str = listOfInts[list_of_ints.index(name)] == int(ca[0])
            if len(rel_quant) > 1:
                for l in range(2, len(rel_quant) + 1):
                    name = 'a_' + str(rel_quant[l - 1] - 1)
                    add_to_variable_list(name)
                    act_str = And(act_str, listOfInts[list_of_ints.index(name)] == int(ca[l - 1]))

            implies_precedent = And(Not(listOfBools[list_of_bools.index(holds1)]), act_str)
            nos_of_subformula += 2

            dicts = []
            # rel_quant = [1,2]
            g = 0
            for l in rel_quant:
                dicts.append(dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                g += 1
            combined_succ = list(itertools.product(*dicts))

            first = True
            prod_left = None
            list_of_ors = []

            for cs in combined_succ:
                f = 0
                prob_succ = 'prob'
                # prob_succ1 = 'prob'
                holds_succ = 'holds'
                d_current = 'd'
                d_succ = 'd'
                p_first = True
                prod_left_part = None
                for l in range(1, n + 1):
                    if l in rel_quant:
                        space = cs[f].find(' ')
                        succ_state = cs[f - 1][0:space]
                        prob_succ += '_' + succ_state
                        holds_succ += '_' + succ_state
                        #prob_succ1 += '_' + succ_state
                        d_succ += '_' + succ_state
                        if p_first:
                            prod_left_part = RealVal(cs[f - 1][space + 1:]).as_fraction()
                            p_first = False
                        else:
                            prod_left_part *= RealVal(cs[f - 1][space + 1:]).as_fraction()
                        f += 1

                    else:
                        prob_succ += '_' + str(0)
                        holds_succ += '_' + str(0)
                        #prob_succ1 += '_' + str(0)
                        d_succ += '_' + str(0)
                        if p_first:
                            prod_left_part = RealVal(1).as_fraction()
                            p_first = False
                        else:
                            prod_left_part *= RealVal(1).as_fraction()
                    d_current += '_' + str(r_state[l - 1])

                prob_succ += '_' + str(index_of_phi)
                add_to_variable_list(prob_succ)
                holds_succ += '_' + str(index_of_phi1)
                # prob_succ1 += '_' + str(index_of_phi)
                # add_to_variable_list(prob_succ1)
                add_to_variable_list(holds_succ)
                d_current += '_' + str(index_of_phi1)
                add_to_variable_list(d_current)
                d_succ += '_' + str(index_of_phi1)
                add_to_variable_list(d_succ)
                prod_left_part *= listOfReals[list_of_reals.index(prob_succ)]

                if first:
                    prod_left = prod_left_part
                    first = False
                else:
                    prod_left += prod_left_part
                nos_of_subformula += 1

                # list_of_ors.append(And(listOfReals[list_of_reals.index(prob_succ1)] > 0,
                #                       listOfReals[list_of_reals.index(d_current)] > listOfReals[
                #                           list_of_reals.index(d_succ)]))
                list_of_ors.append(Or(listOfBools[list_of_bools.index(holds_succ)],
                                      listOfReals[list_of_reals.index(d_current)] > listOfReals[
                                          list_of_reals.index(d_succ)]))

                nos_of_subformula += 2

            implies_antecedent_and1 = listOfReals[list_of_reals.index(prob_phi)] == prod_left
            nos_of_subformula += 1
            prod_right_or = Or([par for par in list_of_ors])
            nos_of_subformula += 1
            implies_antecedent_and2 = Implies(listOfReals[list_of_reals.index(prob_phi)] > 0, prod_right_or)
            nos_of_subformula += 1
            implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
            nos_of_subformula += 1
            s.add(And(first_implies, Implies(implies_precedent, implies_antecedent)))
            nos_of_subformula += 1
            f_pointer.write(str(And(first_implies, Implies(implies_precedent, implies_antecedent))))
            f_pointer.write("\n")

        while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
            r_state[i] = 0
            index[i] = 0
            i = i - 1
            # k = i - 1
            # flago = False
            # while k >= 0:
            #     if k + 1 in rel_quant:
            #         flago = True
            #         break
            #     else:
            #         k -= 1
            #     if flago and (i + 1) in rel_quant and k >= 0 and index[k] < (len(model.states) - 1):
            #         # special case when the current quantifier is relevant but it has reached the end of model
            #         # states. So we increase the previous quantifier value and continue with current quantifier
            #         index[i - 1] += 1
            #         r_state[i - 1] += 1
            #         flag = True
            #     else:
            #         i = i - 1
            # if flag:
            #     flag = False
            #     continue

        if i >= 0:
            index[i] = index[i] + 1
            r_state[i] = index[i]

    print("Done with future")
    return rel_quant


def Semantics(model, formula_duplicate, n):
    global nos_of_subformula
    r_state = [0 for ind in range(n)]
    rel_quant = []
    if formula_duplicate.data == 'true':
        print("Starting with true")
        index_of_phi = list_of_subformula.index(formula_duplicate)
        name = "holds"
        for ind in r_state:
            name += "_" + str(ind)
        name += '_' + str(index_of_phi)
        add_to_variable_list(name)
        s.add(listOfBools[list_of_bools.index(name)])
        nos_of_subformula += 1
        print("Done with true")
        return rel_quant

    elif formula_duplicate.data == 'var':  # var handles the inside varname
        ap_name = formula_duplicate.children[0].children[0].value
        relevant_quantifier = int(formula_duplicate.children[0].children[1].value[1])
        labeling = model.labeling
        rel_quant.append(relevant_quantifier)  # n = no.of quantifier, k = no. of state in the model
        and_for_yes = set()
        and_for_no = set()
        list_of_state_with_ap = []
        index = []
        index_of_phi = list_of_subformula.index(formula_duplicate)
        for state in model.states:
            if ap_name in labeling.get_labels_of_state(state.id):
                list_of_state_with_ap.append(state.id)
        for j in range(0, n):
            index.append(0)
        i = n - 1
        # index[i] = 0
        while i >= 0:
            name = 'holds'
            for ind in r_state:
                name += "_" + str(ind)
            name += '_' + str(index_of_phi)
            add_to_variable_list(name)
            if r_state[relevant_quantifier - 1] in list_of_state_with_ap:
                and_for_yes.add(listOfBools[list_of_bools.index(name)])
            else:
                and_for_no.add(Not(listOfBools[list_of_bools.index(name)]))
            while i >= 0 and (index[i] == (len(model.states) - 1) or (relevant_quantifier - 1) != i):
                r_state[i] = 0
                index[i] = 0
                i = i - 1
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        zz = And(And([par for par in list(and_for_yes)]), And([par for par in list(and_for_no)]))
        s.add(And(And([par for par in list(and_for_yes)]), And([par for par in list(and_for_no)])))
        f_pointer.write("Variable : " + str(ap_name) + "\n")
        f_pointer.write(str(zz))
        f_pointer.write("\n")
        nos_of_subformula += 3
        and_for_yes.clear()
        and_for_no.clear()
        index.clear()
        print("Done with var " + str(ap_name))
        return rel_quant

    elif formula_duplicate.data == 'and_op':
        rel_quant1 = Semantics(model, formula_duplicate.children[0], n)
        rel_quant.extend(rel_quant1)
        rel_quant2 = Semantics(model, formula_duplicate.children[1], n)
        rel_quant.extend(rel_quant2)
        tmp_set = set(rel_quant)
        rel_quant = list(tmp_set)
        # rel_quant[1] = 1
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_of_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_of_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        # n = no.of quantifier, k = no. of state in the model
        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        f_pointer.write("And :\n")
        while i >= 0:
            name1 = 'holds'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    name2 += "_" + str(r_state[ind])
                else:
                    name2 += "_" + str(0)
            name2 += '_' + str(index_of_phi1)
            add_to_variable_list(name2)
            name3 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    name3 += "_" + str(r_state[ind])
                else:
                    name3 += "_" + str(0)
            name3 += '_' + str(index_of_phi2)
            add_to_variable_list(name3)
            first_and = And(listOfBools[list_of_bools.index(name1)], listOfBools[list_of_bools.index(name2)],
                            listOfBools[list_of_bools.index(name3)])
            nos_of_subformula += 1
            second_and = And(Not(listOfBools[list_of_bools.index(name1)]),
                             Or(Not(listOfBools[list_of_bools.index(name2)]),
                                Not(listOfBools[list_of_bools.index(name3)])))
            nos_of_subformula += 1
            s.add(Or(first_and, second_and))

            f_pointer.write(str(Or(first_and, second_and)))
            f_pointer.write("\n")
            nos_of_subformula += 1
            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and k >= 0 and index[k] < (len(model.states) - 1):  # special case
                    # when the current quantifier is relevant but it has reached the end of model states. So we
                    # increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]

        print("Done with and")
        return rel_quant

    elif formula_duplicate.data == 'neg_op':
        print("Starting with neg")
        rel_quant.extend(Semantics(model, formula_duplicate.children[0], n))
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_of_phi1 = list_of_subformula.index(formula_duplicate.children[0])

        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            name1 = 'holds'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'holds'
            for ind in r_state:
                name2 += "_" + str(ind)
            name2 += '_' + str(index_of_phi1)
            add_to_variable_list(name2)
            # xor_pair = Xor(listOfBools[list_of_bools.index(name1)], listOfBools[list_of_bools.index(name2)])
            s.add(Xor(listOfBools[list_of_bools.index(name1)], listOfBools[list_of_bools.index(name2)]))
            f_pointer.write("Negation :\n")
            f_pointer.write(str(Xor(listOfBools[list_of_bools.index(name1)], listOfBools[list_of_bools.index(name2)])))
            f_pointer.write("\n")
            nos_of_subformula += 1
            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and (k) >= 0 and index[k] < (len(
                        model.states) - 1):  # special case when the current quantifier is relevant but it has reached the end of model states. SO we increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        print("Done with neg")
        return rel_quant

    elif formula_duplicate.data == 'less_prob':  # yet to be optimized
        Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        Semantics(model, formula_duplicate.children[1], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        for li in combined_list_of_states:
            name1 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi)
            add_to_variable_list(name1)
            name2 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1)
            add_to_variable_list(name2)
            name3 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2)
            add_to_variable_list(name3)
            and_less = And(listOfBools[list_of_bools.index(name1)],
                           listOfReals[list_of_reals.index(name2)] < listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_greateq = And(Not(listOfBools[list_of_bools.index(name1)]),
                              listOfReals[list_of_reals.index(name2)] >= listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_less, and_greateq))
            nos_of_subformula += 1
        print("Done with less_prob")
    elif formula_duplicate.data == 'greater_prob':  # yet to be optimized
        Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        Semantics(model, formula_duplicate.children[1], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        for li in combined_list_of_states:
            name1 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi)
            add_to_variable_list(name1)
            name2 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1)
            add_to_variable_list(name2)
            name3 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2)
            add_to_variable_list(name3)
            and_great = And(listOfBools[list_of_bools.index(name1)],
                            listOfReals[list_of_reals.index(name2)] > listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_lesseq = And(Not(listOfBools[list_of_bools.index(name1)]),
                             listOfReals[list_of_reals.index(name2)] <= listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_great, and_lesseq))
            nos_of_subformula += 1
        print("Done with greater_prob")
    elif formula_duplicate.data == 'equal_prob':
        rel_quant1 = Semantics(model, formula_duplicate.children[0], n)
        rel_quant2 = Semantics(model, formula_duplicate.children[1], n)
        rel_quant.extend(rel_quant1)
        rel_quant.extend(rel_quant2)
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_of_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_of_phi2 = list_of_subformula.index(formula_duplicate.children[1])

        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        f_pointer.write("Equal probability :\n")
        while i >= 0:
            name1 = 'holds'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    name2 += "_" + str(r_state[ind])
                else:
                    name2 += "_" + str(0)
            name2 += '_' + str(index_of_phi1)
            add_to_variable_list(name2)
            name3 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    name3 += "_" + str(r_state[ind])
                else:
                    name3 += "_" + str(0)
            name3 += '_' + str(index_of_phi2)
            add_to_variable_list(name3)
            and_eq = And(listOfBools[list_of_bools.index(name1)],
                         listOfReals[list_of_reals.index(name2)] == listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_not_eq = And(Not(listOfBools[list_of_bools.index(name1)]),
                             listOfReals[list_of_reals.index(name2)] != listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_eq, and_not_eq))
            nos_of_subformula += 1

            f_pointer.write(str(Or(and_eq, and_not_eq)))
            f_pointer.write("\n")
            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and (k) >= 0 and index[k] < (len(
                        model.states) - 1):  # special case when the current quantifier is relevant but it has reached the end of model states. SO we increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        print("Done with equal_prob")
        return rel_quant

    elif formula_duplicate.data == 'calc_probability':
        child = formula_duplicate.children[0]
        print("Starting probability")
        if child.data == 'calc_next':
            SemanticsNext(model, formula_duplicate, combined_list_of_states, n)
        elif child.data == 'calc_until_unbounded':
            SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n)
        elif child.data == 'calc_until_bounded':
            SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)
        elif child.data == 'calc_future':
            rel_quant.extend(SemanticsFuture(model, formula_duplicate, n))
        print("Done with probability")
        return rel_quant
    elif formula_duplicate.data == 'calc_until_unbounded':  # might be redundant
        print("Starting until unbounded")
        SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n)
    elif formula_duplicate.data == 'calc_until_bounded':
        SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)
    elif formula_duplicate.data == 'const':  # yet to be optimized
        c = formula_duplicate.children[0].value
        list_of_probs = []
        for li in combined_list_of_states:
            name1 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate))
            add_to_variable_list(name1)
            list_of_probs.append(listOfReals[list_of_reals.index(name1)] == c)
            nos_of_subformula += 1
        s.add(And([par for par in list_of_probs]))
        nos_of_subformula += 1
        print("Done with constant")
    elif formula_duplicate.data in ['add_prob', 'minus_prob', 'mul_prob']:  # yet to be optimized
        left = formula_duplicate.children[0]
        index_left = list_of_subformula.index(left)
        right = formula_duplicate.children[1]
        index_right = list_of_subformula.index(right)
        Semantics(model, left, combined_list_of_states, n)
        Semantics(model, right, combined_list_of_states, n)
        for li in combined_list_of_states:
            name1 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left)
            add_to_variable_list(name1)
            name2 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right)
            add_to_variable_list(name2)
            name3 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate))
            add_to_variable_list(name3)
            if formula_duplicate.data == 'add_prob':
                s.add(listOfReals[list_of_reals.index(name3)] == (
                        listOfReals[list_of_reals.index(name1)] + listOfReals[list_of_reals.index(name2)]))
                nos_of_subformula += 2
            elif formula_duplicate.data == 'minus_prob':
                s.add(listOfReals[list_of_reals.index(name3)] == (
                        listOfReals[list_of_reals.index(name1)] - listOfReals[list_of_reals.index(name2)]))
                nos_of_subformula += 2
            elif formula_duplicate.data == 'mul_prob':
                s.add(listOfReals[list_of_reals.index(name3)] == (
                        listOfReals[list_of_reals.index(name1)] * listOfReals[list_of_reals.index(name2)]))
                nos_of_subformula += 2


def Truth(model, formula_initial, combined_list_of_states, n):
    global nos_of_subformula
    list_of_AV = []  # will have the OR, AND according to the quantifier in that index in the formula
    f_pointer.write("Truth :\n")

    while len(formula_initial.children) > 0 and type(formula_initial.children[0]) == Token:
        if formula_initial.data in ['exist_scheduler', 'forall_scheduler']:
            formula_initial = formula_initial.children[1]
        elif formula_initial.data == 'exist':
            list_of_AV.append('V')
            formula_initial = formula_initial.children[1]
        elif formula_initial.data == 'forall':
            list_of_AV.append('A')
            formula_initial = formula_initial.children[1]
    index_of_phi = list_of_subformula.index(formula_initial)
    list_of_holds = []

    print("Starting big loop in Truth")
    for i in range(len(combined_list_of_states)):
        name = "holds_"
        for j in range(n):
            name += str(combined_list_of_states[i][j]) + "_"
        name += str(index_of_phi)
        add_to_variable_list(name)
        list_of_holds.append(listOfBools[list_of_bools.index(name)])

    list_of_holds_replace = []
    for i in range(n - 1, -1, -1):
        count = -1
        limit = len(list_of_holds)
        quo = 0
        for j in range(limit):
            count += 1
            # temp_list.append(list_of_holds[limit])
            if count == len(model.states) - 1:
                index = quo * len(model.states)
                if list_of_AV[i] == 'V':
                    list_of_holds_replace.append(Or([par for par in list_of_holds[index:index + count + 1]]))
                elif list_of_AV[i] == 'A':
                    list_of_holds_replace.append(And([par for par in list_of_holds[index:index + count + 1]]))
                count = -1
                quo += 1
        list_of_holds = copy.deepcopy(list_of_holds_replace)
        list_of_holds_replace.clear()
        f_pointer.write(str(list_of_holds))
        f_pointer.write("\n")
    s.add(list_of_holds[0])

    print("Truth done")


def add_to_subformula_list(formula_phi):  # add as you go any new subformula part as needed
    if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist', 'forall']:
        formula_phi = formula_phi.children[1]
        add_to_subformula_list(formula_phi)
    elif formula_phi.data in ['and_op', 'less_prob', 'greater_prob', 'add_prob', 'minus_prob', 'mul_prob',
                              'calc_until_unbounded', 'equal_prob']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
        left_child = formula_phi.children[0]
        add_to_subformula_list(left_child)
        right_child = formula_phi.children[1]
        add_to_subformula_list(right_child)
    elif formula_phi.data in ['var', 'true', 'const']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
    elif formula_phi.data in ['calc_next', 'neg_op', 'calc_future']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
        add_to_subformula_list(formula_phi.children[0])
    elif formula_phi.data in ['calc_probability']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
        add_to_subformula_list(formula_phi.children[0])
    elif formula_phi.data in ['calc_until_bounded']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
        left_child = formula_phi.children[0]
        add_to_subformula_list(left_child)
        right_child = formula_phi.children[3]
        add_to_subformula_list(right_child)


def add_to_variable_list(name):
    if name[0] == 'h' and name not in list_of_bools:
        list_of_bools.append(name)
        listOfBools.append(Bool(name))
    elif name[0] in ['p', 'd'] and name not in list_of_reals:
        list_of_reals.append(name)
        listOfReals.append(Real(name))
    elif name[0] == 'a' and name not in list_of_ints:
        list_of_ints.append(name)
        listOfInts.append(Int(name))


def check_result():
    starting = time.process_time()
    t = s.check()
    print("Time required by z3: " + str(time.process_time() - starting))
    if t == sat:
        model = s.model()
        li_h = dict()
        for li in model:
            if li.name()[0] == 'h':
                li_h[li.name()] = model[li]
                print(str(li.name()) + '=' + str(model[li]))
        li_p = dict()
        for li in model:
            if li.name()[0] == 'p':
                li_p[li.name()] = model[li]
                print(str(li.name()) + '=' + str(model[li]))
        li_a = dict()
        for li in model:
            if li.name()[0] == 'a':
                li_a[li.name()] = model[li]
                print(str(li.name()) + '=' + str(model[li]))
        li_d = dict()
        for li in model:
            if li.name()[0] == 'd':
                li_d[li.name()] = model[li]
                print(str(li.name()) + '=' + str(model[li]))
    print(s.statistics())
    print("\n")
    print("Number of variables: " + str(len(list_of_ints) + len(list_of_reals) + len(list_of_bools)))
    print("Number of formula checked: " + str(nos_of_subformula))
    if t.r == 1:
        return True
    elif t.r == -1:
        return False


def main_smt_encoding(model, formula_initial, formula):
    global nos_of_subformula
    list_of_states = []
    starttime = time.process_time()
    f_pointer.write("Actions :\n")
    for state in model.states:
        list_of_eqns = []
        name = "a_" + str(state.id)  # a_1 means action for state 1
        add_to_variable_list(name)
        for action in state.actions:
            list_of_eqns.append(listOfInts[list_of_ints.index(name)] == int(action.id))
        if len(list_of_eqns) == 1:
            s.add(list_of_eqns[0])
            f_pointer.write(str(list_of_eqns[0]))
        else:
            s.add(Or([par for par in list_of_eqns]))
            f_pointer.write(str(Or([par for par in list_of_eqns])))
        nos_of_subformula += 1

        f_pointer.write("\n")
    n_of_state_quantifier = 0
    formula_duplicate = formula_initial
    while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist', 'forall']:
            n_of_state_quantifier += 1
            formula_duplicate = formula_duplicate.children[1]
    for state in model.states:
        list_of_states.append(state.id)
    combined_list_of_states = list(itertools.product(list_of_states, repeat=n_of_state_quantifier))
    if formula_initial.data == 'exist_scheduler':
        add_to_subformula_list(formula_initial)
        print("Calling Truth...")
        Truth(model, formula_initial, combined_list_of_states, n_of_state_quantifier)
        print("Calling Semantics...")
        Semantics(model, formula_duplicate, n_of_state_quantifier)
        # s.add(listOfReals[list_of_reals.index('prob_0_0_8')] == listOfReals[list_of_reals.index('prob_0_1_11')])
        # f_pointer.write(str(listOfReals[list_of_reals.index('prob_0_0_8')] == listOfReals[list_of_reals.index('prob_0_1_11')]))
        # f_pointer.write("\n")
        # s.add(listOfReals[list_of_reals.index('d_0_1_12')] == 1)
        # f_pointer.write(str(listOfReals[list_of_reals.index('d_0_1_12')] == 1))
        # f_pointer.write("\n")
        # s.add(listOfReals[list_of_reals.index('d_0_4_12')] == 0.6)
        # f_pointer.write(str(listOfReals[list_of_reals.index('d_0_4_12')] == 0.6))
        # f_pointer.write("\n")
        # s.add(listOfReals[list_of_reals.index('d_0_5_12')] == 0.4)
        # f_pointer.write(str(listOfReals[list_of_reals.index('d_0_5_12')] == 0.4))
        # f_pointer.write("\n")
        # s.add(listOfReals[list_of_reals.index('d_0_3_12')] == 2)
        # f_pointer.write(str(listOfReals[list_of_reals.index('d_0_3_12')] == 2))
        # f_pointer.write("\n")
        smt_end_time = time.process_time() - starttime
        print("Time to encode: " + str(smt_end_time))
        print("Checking...")
        if check_result():
            return True
        else:
            return False

    elif formula_initial.data == 'forall_scheduler':
        new_formula = ''
        i = 0

        first = True
        while i < len(formula):
            jjj = formula[i]  # just to see what char we are accessing. Can be removed later.
            if formula[i] == 'E':
                if formula[i + 1] == 'S':
                    new_formula += formula[i] + formula[i + 1]
                    i += 2
                elif formula[i + 1] == ' ':
                    new_formula += 'A' + formula[i + 1]
                    i += 2
            elif formula[i] == 'A':
                if formula[i + 1] == 'S':
                    new_formula += 'E' + formula[i + 1]
                    i += 2
                elif formula[i + 1] == ' ':
                    new_formula += 'E' + formula[i + 1]
                    i += 2
            else:
                if first and formula[i - 1] == ' ' and formula[i - 2] == '.':
                    if formula[i] == '~':
                        # added this to avoid double negation for exist. Might want to remove the extra brace around
                        # the formula due to previous not.
                        first = False
                        i += 1
                        continue
                    else:
                        new_formula += '~'
                    first = False
                new_formula += formula[i]
                i += 1
        new_parsed_formula = parser.parse(new_formula)
        formula_duplicate = new_parsed_formula
        n_of_state_quantifier = 0
        while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
            if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
                formula_duplicate = formula_duplicate.children[1]
            elif formula_duplicate.data in ['exist', 'forall']:
                n_of_state_quantifier += 1
                formula_duplicate = formula_duplicate.children[1]
        add_to_subformula_list(new_parsed_formula)
        print("Calling Truth...")
        Truth(model, new_parsed_formula, combined_list_of_states, n_of_state_quantifier)
        print("Calling Semantics...")
        Semantics(model, formula_duplicate, n_of_state_quantifier)
        smt_end_time = time.process_time() - starttime
        print("Time to encode: " + str(smt_end_time))
        print("Checking...")
        if check_result():
            return False
        else:
            return True


def build_model_manually_synthesis(initial_mod):
    nr_states = 6
    nr_choices = 6

    builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, force_dimensions=False,
                                               has_custom_row_grouping=True, row_groups=0)

    builder.new_row_group(0)
    builder.add_next_value(0, 2, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 3, stormpy.Rational(5) / stormpy.Rational(6))

    builder.new_row_group(1)
    builder.add_next_value(1, 3, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(1, 4, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(2)
    builder.add_next_value(2, 2, stormpy.Rational(1))

    builder.new_row_group(3)
    builder.add_next_value(3, 3, stormpy.Rational(1))

    builder.new_row_group(4)
    builder.add_next_value(4, 3, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 5, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(5)
    builder.add_next_value(5, 2, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 4, stormpy.Rational(1) / stormpy.Rational(2))

    transition_matrix = builder.build()

    state_labeling = initial_mod.labeling

    components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix, state_labeling=state_labeling)
    mdp = stormpy.storage.SparseExactMdp(components)
    initial_model = mdp
    return initial_model


def build_model_manually_synthesis0(initial_mod):
    builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, force_dimensions=False,
                                               has_custom_row_grouping=True, row_groups=0)

    builder.new_row_group(0)
    builder.add_next_value(0, 2, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 3, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 4, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 5, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 6, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 7, stormpy.Rational(1) / stormpy.Rational(6))

    builder.new_row_group(1)
    builder.add_next_value(1, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(1, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(6, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(6, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(7, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(7, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(8, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(8, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(9, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(9, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(14, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(14, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(15, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(15, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(17, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(17, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(18, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(18, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(19, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(19, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(20, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(20, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(21, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(21, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(22, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(22, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(23, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(23, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(24, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(24, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(25, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(25, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(26, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(26, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(27, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(27, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(28, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(28, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(29, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(29, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(30, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(30, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(31, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(31, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(32, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(32, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(33, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(33, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(34, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(34, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(35, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(35, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(36, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(36, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(37, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(37, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(38, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(38, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(39, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(39, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(40, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(40, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(41, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(41, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(42, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(42, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(43, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(43, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(44, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(44, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(45, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(45, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(46, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(46, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(47, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(47, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(48, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(48, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(49, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(49, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(50, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(50, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(51, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(51, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(52, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(52, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(53, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(53, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(54, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(54, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(55, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(55, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(56, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(56, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(57, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(57, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(58, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(58, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(59, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(59, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(60, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(60, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(61, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(61, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(62, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(62, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(63, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(63, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(64)
    builder.add_next_value(64, 2, stormpy.Rational(1))

    builder.new_row_group(65)
    builder.add_next_value(65, 3, stormpy.Rational(1))

    builder.new_row_group(66)
    builder.add_next_value(66, 4, stormpy.Rational(1))

    builder.new_row_group(67)
    builder.add_next_value(67, 5, stormpy.Rational(1))

    builder.new_row_group(68)
    builder.add_next_value(68, 6, stormpy.Rational(1))

    builder.new_row_group(69)
    builder.add_next_value(69, 7, stormpy.Rational(1))

    builder.new_row_group(70)
    builder.add_next_value(70, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(70, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(71, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(71, 8, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(72)
    builder.add_next_value(72, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(72, 13, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(73)
    builder.add_next_value(73, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(73, 14, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(74)
    builder.add_next_value(74, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(74, 16, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(75)
    builder.add_next_value(75, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(75, 18, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(76)
    builder.add_next_value(76, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(76, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(77)
    builder.add_next_value(77, 14, stormpy.Rational(1))

    builder.new_row_group(78)
    builder.add_next_value(78, 15, stormpy.Rational(1))

    builder.new_row_group(79)
    builder.add_next_value(79, 16, stormpy.Rational(1))

    builder.new_row_group(80)
    builder.add_next_value(80, 17, stormpy.Rational(1))

    builder.new_row_group(81)
    builder.add_next_value(81, 18, stormpy.Rational(1))

    builder.new_row_group(82)
    builder.add_next_value(82, 19, stormpy.Rational(1))

    transition_matrix = builder.build()

    state_labeling = initial_mod.labeling

    components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix, state_labeling=state_labeling)
    mdp = stormpy.storage.SparseExactMdp(components)
    initial_model = mdp
    return initial_model


def build_model_manually_synthesis0_1(initial_mod):
    builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, force_dimensions=False,
                                               has_custom_row_grouping=True, row_groups=0)

    builder.new_row_group(0)
    builder.add_next_value(0, 2, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 3, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 4, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 5, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 6, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 7, stormpy.Rational(1) / stormpy.Rational(6))

    builder.new_row_group(1)
    builder.add_next_value(1, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(1, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(6, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(6, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(7, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(7, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(8, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(8, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(9, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(9, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(14, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(14, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(15, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(15, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(17, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(17, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(18, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(18, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(19, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(19, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(20, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(20, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(21, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(21, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(22, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(22, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(23, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(23, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(24, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(24, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(25, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(25, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(26, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(26, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(27, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(27, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(28, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(28, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(29, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(29, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(30, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(30, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(31, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(31, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(32, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(32, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(33, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(33, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(34, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(34, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(35, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(35, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(36, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(36, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(37, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(37, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(38, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(38, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(39, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(39, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(40, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(40, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(41, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(41, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(42, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(42, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(43, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(43, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(44, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(44, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(45, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(45, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(46, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(46, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(47, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(47, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(48, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(48, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(49, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(49, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(50, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(50, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(51, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(51, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(52, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(52, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(53, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(53, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(54, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(54, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(55, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(55, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(56, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(56, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(57, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(57, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(58, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(58, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(59, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(59, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(60, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(60, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(61, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(61, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(62, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(62, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(63, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(63, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(64)
    builder.add_next_value(64, 2, stormpy.Rational(1))

    builder.new_row_group(65)
    builder.add_next_value(65, 3, stormpy.Rational(1))

    builder.new_row_group(66)
    builder.add_next_value(66, 4, stormpy.Rational(1))

    builder.new_row_group(67)
    builder.add_next_value(67, 5, stormpy.Rational(1))

    builder.new_row_group(68)
    builder.add_next_value(68, 6, stormpy.Rational(1))

    builder.new_row_group(69)
    builder.add_next_value(69, 7, stormpy.Rational(1))

    builder.new_row_group(70)
    builder.add_next_value(70, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(70, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(71, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(71, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(72, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(72, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(73, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(73, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(74, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(74, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(75, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(75, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(76, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(76, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(77, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(77, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(78, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(78, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(79, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(79, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(80, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(80, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(81, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(81, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(82, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(82, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(83, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(83, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(84, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(84, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(85, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(85, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(86, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(86, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(87, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(87, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(88, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(88, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(89, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(89, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(90, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(90, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(91, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(91, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(92, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(92, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(93, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(93, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(94, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(94, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(95, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(95, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(96, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(96, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(97, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(97, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(98, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(98, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(99, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(99, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(100, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(100, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(101, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(101, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(102, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(102, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(103, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(103, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(104, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(104, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(105, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(105, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(106, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(106, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(107, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(107, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(108, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(108, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(109, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(109, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(110, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(110, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(111, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(111, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(112, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(112, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(113, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(113, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(114, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(114, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(115, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(115, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(116, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(116, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(117, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(117, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(118, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(118, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(119, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(119, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(120, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(120, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(121, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(121, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(122, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(122, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(123, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(123, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(124, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(124, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(125, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(125, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(126, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(126, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(127, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(127, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(128, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(128, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(129, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(129, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(130, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(130, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(131, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(131, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(132, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(132, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(133)
    builder.add_next_value(133, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(133, 13, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(134)
    builder.add_next_value(134, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(134, 14, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(135)
    builder.add_next_value(135, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(135, 16, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(136)
    builder.add_next_value(136, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(136, 18, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(137)
    builder.add_next_value(137, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(137, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(138)
    builder.add_next_value(138, 14, stormpy.Rational(1))

    builder.new_row_group(139)
    builder.add_next_value(139, 15, stormpy.Rational(1))

    builder.new_row_group(140)
    builder.add_next_value(140, 16, stormpy.Rational(1))

    builder.new_row_group(141)
    builder.add_next_value(141, 17, stormpy.Rational(1))

    builder.new_row_group(142)
    builder.add_next_value(142, 18, stormpy.Rational(1))

    builder.new_row_group(143)
    builder.add_next_value(143, 19, stormpy.Rational(1))

    transition_matrix = builder.build()

    state_labeling = initial_mod.labeling

    components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix, state_labeling=state_labeling)
    mdp = stormpy.storage.SparseExactMdp(components)
    initial_model = mdp
    return initial_model


def build_model_manually_synthesis_reduced(initial_mod):
    builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, force_dimensions=False,
                                               has_custom_row_grouping=True, row_groups=0)

    builder.new_row_group(0)
    builder.add_next_value(0, 2, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 3, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 4, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 5, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 6, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 7, stormpy.Rational(1) / stormpy.Rational(6))

    builder.new_row_group(1)
    builder.add_next_value(1, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(1, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 11, stormpy.Rational(1) / stormpy.Rational(4))
    builder.add_next_value(2, 12, stormpy.Rational(1) / stormpy.Rational(4))
    builder.add_next_value(3, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 14, stormpy.Rational(1) / stormpy.Rational(4))
    builder.add_next_value(3, 15, stormpy.Rational(1) / stormpy.Rational(4))

    builder.new_row_group(4)
    builder.add_next_value(4, 2, stormpy.Rational(1))

    builder.new_row_group(5)
    builder.add_next_value(5, 3, stormpy.Rational(1))

    builder.new_row_group(6)
    builder.add_next_value(6, 4, stormpy.Rational(1))

    builder.new_row_group(7)
    builder.add_next_value(7, 5, stormpy.Rational(1))

    builder.new_row_group(8)
    builder.add_next_value(8, 6, stormpy.Rational(1))

    builder.new_row_group(9)
    builder.add_next_value(9, 7, stormpy.Rational(1))

    builder.new_row_group(10)
    builder.add_next_value(10, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 11, stormpy.Rational(1) / stormpy.Rational(4))
    builder.add_next_value(10, 12, stormpy.Rational(1) / stormpy.Rational(4))
    builder.add_next_value(11, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 8, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(12)
    builder.add_next_value(12, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 14, stormpy.Rational(1) / stormpy.Rational(4))
    builder.add_next_value(12, 15, stormpy.Rational(1) / stormpy.Rational(4))

    builder.new_row_group(13)
    builder.add_next_value(13, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 16, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(14)
    builder.add_next_value(14, 11, stormpy.Rational(1))

    builder.new_row_group(15)
    builder.add_next_value(15, 12, stormpy.Rational(1))

    builder.new_row_group(16)
    builder.add_next_value(16, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 17, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(17)
    builder.add_next_value(17, 14, stormpy.Rational(1))

    builder.new_row_group(18)
    builder.add_next_value(18, 15, stormpy.Rational(1))

    builder.new_row_group(19)
    builder.add_next_value(19, 16, stormpy.Rational(1))

    builder.new_row_group(20)
    builder.add_next_value(20, 17, stormpy.Rational(1))

    transition_matrix = builder.build()

    state_labeling = initial_mod.labeling

    components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix, state_labeling=state_labeling)
    mdp = stormpy.storage.SparseExactMdp(components)
    initial_model = mdp
    return initial_model


def build_model_manually_conformance5int(initial_mod):
    builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, force_dimensions=False,
                                               has_custom_row_grouping=True, row_groups=0)

    builder.new_row_group(0)
    builder.add_next_value(0, 2, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 3, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 4, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 5, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 6, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 7, stormpy.Rational(1) / stormpy.Rational(6))

    builder.new_row_group(1)
    builder.add_next_value(1, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(1, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(6, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(6, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(7, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(7, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(8, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(8, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(9, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(9, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(14, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(14, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(15, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(15, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(17, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(17, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(18, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(18, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(19, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(19, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(20, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(20, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(21, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(21, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(22, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(22, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(23, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(23, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(24, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(24, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(25, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(25, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(26, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(26, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(27, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(27, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(28, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(28, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(29, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(29, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(30, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(30, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(31, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(31, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(32, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(32, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(33, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(33, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(34, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(34, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(35, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(35, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(36, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(36, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(37, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(37, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(38, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(38, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(39, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(39, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(40, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(40, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(41, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(41, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(42, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(42, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(43, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(43, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(44, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(44, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(45, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(45, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(46, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(46, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(47, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(47, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(48, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(48, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(49, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(49, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(50, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(50, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(51, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(51, 18, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(52)
    builder.add_next_value(52, 2, stormpy.Rational(1))

    builder.new_row_group(53)
    builder.add_next_value(53, 3, stormpy.Rational(1))

    builder.new_row_group(54)
    builder.add_next_value(54, 4, stormpy.Rational(1))

    builder.new_row_group(55)
    builder.add_next_value(55, 5, stormpy.Rational(1))

    builder.new_row_group(56)
    builder.add_next_value(56, 6, stormpy.Rational(1))

    builder.new_row_group(57)
    builder.add_next_value(57, 7, stormpy.Rational(1))

    builder.new_row_group(58)
    builder.add_next_value(58, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(58, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(59, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(59, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(60, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(60, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(61, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(61, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(62, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(62, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(63, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(63, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(64, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(64, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(65, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(65, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(66, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(66, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(67, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(67, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(68, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(68, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(69, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(69, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(70, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(70, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(71, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(71, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(72, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(72, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(73, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(73, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(74, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(74, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(75, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(75, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(76, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(76, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(77, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(77, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(78, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(78, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(79, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(79, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(80, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(80, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(81, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(81, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(82, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(82, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(83, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(83, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(84, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(84, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(85, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(85, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(86, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(86, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(87, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(87, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(88, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(88, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(89, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(89, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(90, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(90, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(91, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(91, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(92, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(92, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(93, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(93, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(94, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(94, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(95, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(95, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(96, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(96, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(97, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(97, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(98, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(98, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(99, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(99, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(100, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(100, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(101, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(101, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(102, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(102, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(103, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(103, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(104, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(104, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(105, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(105, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(106, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(106, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(107, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(107, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(108, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(108, 18, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(109)
    builder.add_next_value(109, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(109, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(110, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(110, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(111, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(111, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(112, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(112, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(113, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(113, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(114, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(114, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(115, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(115, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(116, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(116, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(117, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(117, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(118, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(118, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(119, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(119, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(120, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(120, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(121, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(121, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(122, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(122, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(123, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(123, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(124, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(124, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(125, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(125, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(126, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(126, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(127, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(127, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(128, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(128, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(129, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(129, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(130, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(130, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(131, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(131, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(132, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(132, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(133, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(133, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(134, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(134, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(135, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(135, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(136, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(136, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(137, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(137, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(138, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(138, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(139, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(139, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(140, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(140, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(141, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(141, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(142, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(142, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(143, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(143, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(144, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(144, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(145, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(145, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(146, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(146, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(147, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(147, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(148, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(148, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(149, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(149, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(150, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(150, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(151, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(151, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(152, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(152, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(153, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(153, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(154, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(154, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(155, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(155, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(156, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(156, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(157, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(157, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(158, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(158, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(159, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(159, 18, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(160)
    builder.add_next_value(160, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(160, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(161, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(161, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(162, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(162, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(163, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(163, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(164, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(164, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(165, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(165, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(166, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(166, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(167, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(167, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(168, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(168, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(169, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(169, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(170, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(170, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(171, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(171, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(172, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(172, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(173, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(173, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(174, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(174, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(175, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(175, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(176, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(176, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(177, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(177, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(178, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(178, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(179, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(179, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(180, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(180, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(181, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(181, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(182, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(182, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(183, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(183, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(184, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(184, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(185, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(185, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(186, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(186, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(187, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(187, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(188, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(188, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(189, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(189, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(190, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(190, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(191, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(191, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(192, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(192, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(193, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(193, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(194, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(194, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(195, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(195, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(196, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(196, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(197, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(197, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(198, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(198, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(199, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(199, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(200, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(200, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(201, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(201, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(202, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(202, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(203, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(203, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(204, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(204, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(205, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(205, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(206, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(206, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(207, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(207, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(208, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(208, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(209, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(209, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(210, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(210, 18, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(211)
    builder.add_next_value(211, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(211, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(212, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(212, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(213, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(213, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(214, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(214, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(215, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(215, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(216, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(216, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(217, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(217, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(218, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(218, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(219, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(219, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(220, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(220, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(221, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(221, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(222, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(222, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(223, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(223, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(224, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(224, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(225, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(225, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(226, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(226, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(227, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(227, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(228, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(228, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(229, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(229, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(230, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(230, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(231, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(231, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(232, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(232, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(233, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(233, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(234, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(234, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(235, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(235, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(236, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(236, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(237, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(237, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(238, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(238, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(239, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(239, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(240, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(240, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(241, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(241, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(242, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(242, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(243, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(243, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(244, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(244, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(245, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(245, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(246, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(246, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(247, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(247, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(248, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(248, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(249, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(249, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(250, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(250, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(251, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(251, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(252, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(252, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(253, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(253, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(254, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(254, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(255, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(255, 17, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(256)
    builder.add_next_value(256, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(256, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(257, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(257, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(258, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(258, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(259, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(259, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(260, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(260, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(261, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(261, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(262, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(262, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(263, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(263, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(264, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(264, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(265, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(265, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(266, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(266, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(267, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(267, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(268, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(268, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(269, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(269, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(270, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(270, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(271, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(271, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(272, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(272, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(273, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(273, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(274, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(274, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(275, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(275, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(276, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(276, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(277, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(277, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(278, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(278, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(279, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(279, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(280, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(280, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(281, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(281, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(282, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(282, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(283, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(283, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(284, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(284, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(285, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(285, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(286, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(286, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(287, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(287, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(288, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(288, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(289, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(289, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(290, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(290, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(291, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(291, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(292, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(292, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(293, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(293, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(294, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(294, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(295, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(295, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(296, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(296, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(297, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(297, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(298, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(298, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(299, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(299, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(300, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(300, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(301, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(301, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(302, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(302, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(303, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(303, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(304, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(304, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(305, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(305, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(306, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(306, 18, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(307)
    builder.add_next_value(307, 13, stormpy.Rational(1))

    builder.new_row_group(308)
    builder.add_next_value(308, 14, stormpy.Rational(1))

    builder.new_row_group(309)
    builder.add_next_value(309, 15, stormpy.Rational(1))

    builder.new_row_group(310)
    builder.add_next_value(310, 16, stormpy.Rational(1))

    builder.new_row_group(311)
    builder.add_next_value(311, 17, stormpy.Rational(1))

    builder.new_row_group(312)
    builder.add_next_value(312, 18, stormpy.Rational(1))

    transition_matrix = builder.build()
    state_labeling = initial_mod.labeling
    components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix, state_labeling=state_labeling)
    mdp = stormpy.storage.SparseExactMdp(components)
    initial_model = mdp
    return initial_model


def write_model_for_exact(initial_mod, file):
    path = files._path("encoding_files", file[0], file[1] + '.txt')
    print(path)
    mod_pointer = open(path, "w")
    mod_pointer.write("builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, "
                      "force_dimensions=False, has_custom_row_grouping=True, row_groups=0)\n")
    count_action = 0
    for state in initial_mod.states:
        mod_pointer.write("\nbuilder.new_row_group(" + str(count_action) + ")\n")
        for action in state.actions:
            for tran in action.transitions:
                mod_pointer.write("builder.add_next_value(" + str(count_action) + ", ")
                if tran.value() == 0.5:
                    mod_pointer.write(str(tran.column) + ", stormpy.Rational(1)/ stormpy.Rational(2))\n")
                elif tran.value() == 1:
                    mod_pointer.write(str(tran.column) + ", stormpy.Rational(1))\n")
                else:
                    mod_pointer.write(str(tran.column) + ", stormpy.Rational(" + str(tran.value()) + "))\n")
            count_action += 1

    mod_pointer.write("\ntransition_matrix = builder.build()\n")
    mod_pointer.write("state_labeling = initial_mod.labeling\n")
    mod_pointer.write(
        "components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix, state_labeling=state_labeling)\n")
    mod_pointer.write("mdp = stormpy.storage.SparseExactMdp(components)\n")
    mod_pointer.write("initial_model = mdp\n")
    mod_pointer.write("return initial_model\n")

    mod_pointer.close()


def build_model_manually_synthesis_all(initial_mod):
    builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, force_dimensions=False,
                                               has_custom_row_grouping=True, row_groups=0)

    builder.new_row_group(0)
    builder.add_next_value(0, 2, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 3, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 4, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 5, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 6, stormpy.Rational(1) / stormpy.Rational(6))
    builder.add_next_value(0, 7, stormpy.Rational(1) / stormpy.Rational(6))

    builder.new_row_group(1)
    builder.add_next_value(1, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(1, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(2, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(3, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(4, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(5, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(6, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(6, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(7, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(7, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(8, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(8, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(9, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(9, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(10, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(11, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(12, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(13, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(14, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(14, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(15, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(15, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(16, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(17, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(17, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(18, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(18, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(19, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(19, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(20, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(20, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(21, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(21, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(22, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(22, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(23, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(23, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(24, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(24, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(25, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(25, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(26, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(26, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(27, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(27, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(28, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(28, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(29, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(29, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(30, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(30, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(31, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(31, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(32, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(32, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(33, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(33, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(34, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(34, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(35, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(35, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(36, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(36, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(37, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(37, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(38, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(38, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(39, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(39, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(40, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(40, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(41, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(41, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(42, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(42, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(43, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(43, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(44, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(44, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(45, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(45, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(46, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(46, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(47, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(47, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(48, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(48, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(49, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(49, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(50, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(50, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(51, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(51, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(52, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(52, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(53, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(53, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(54, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(54, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(55, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(55, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(56, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(56, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(57, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(57, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(58, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(58, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(59, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(59, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(60, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(60, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(61, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(61, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(62, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(62, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(63, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(63, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(64)
    builder.add_next_value(64, 2, stormpy.Rational(1))

    builder.new_row_group(65)
    builder.add_next_value(65, 3, stormpy.Rational(1))

    builder.new_row_group(66)
    builder.add_next_value(66, 4, stormpy.Rational(1))

    builder.new_row_group(67)
    builder.add_next_value(67, 5, stormpy.Rational(1))

    builder.new_row_group(68)
    builder.add_next_value(68, 6, stormpy.Rational(1))

    builder.new_row_group(69)
    builder.add_next_value(69, 7, stormpy.Rational(1))

    builder.new_row_group(70)
    builder.add_next_value(70, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(70, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(71, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(71, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(72, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(72, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(73, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(73, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(74, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(74, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(75, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(75, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(76, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(76, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(77, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(77, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(78, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(78, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(79, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(79, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(80, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(80, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(81, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(81, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(82, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(82, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(83, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(83, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(84, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(84, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(85, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(85, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(86, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(86, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(87, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(87, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(88, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(88, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(89, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(89, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(90, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(90, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(91, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(91, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(92, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(92, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(93, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(93, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(94, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(94, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(95, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(95, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(96, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(96, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(97, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(97, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(98, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(98, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(99, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(99, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(100, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(100, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(101, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(101, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(102, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(102, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(103, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(103, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(104, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(104, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(105, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(105, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(106, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(106, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(107, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(107, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(108, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(108, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(109, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(109, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(110, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(110, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(111, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(111, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(112, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(112, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(113, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(113, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(114, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(114, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(115, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(115, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(116, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(116, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(117, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(117, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(118, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(118, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(119, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(119, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(120, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(120, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(121, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(121, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(122, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(122, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(123, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(123, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(124, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(124, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(125, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(125, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(126, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(126, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(127, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(127, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(128, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(128, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(129, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(129, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(130, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(130, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(131, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(131, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(132, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(132, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(133)
    builder.add_next_value(133, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(133, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(134, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(134, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(135, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(135, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(136, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(136, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(137, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(137, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(138, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(138, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(139, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(139, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(140, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(140, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(141, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(141, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(142, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(142, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(143, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(143, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(144, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(144, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(145, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(145, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(146, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(146, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(147, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(147, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(148, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(148, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(149, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(149, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(150, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(150, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(151, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(151, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(152, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(152, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(153, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(153, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(154, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(154, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(155, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(155, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(156, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(156, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(157, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(157, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(158, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(158, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(159, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(159, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(160, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(160, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(161, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(161, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(162, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(162, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(163, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(163, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(164, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(164, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(165, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(165, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(166, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(166, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(167, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(167, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(168, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(168, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(169, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(169, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(170, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(170, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(171, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(171, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(172, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(172, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(173, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(173, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(174, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(174, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(175, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(175, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(176, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(176, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(177, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(177, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(178, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(178, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(179, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(179, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(180, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(180, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(181, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(181, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(182, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(182, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(183, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(183, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(184, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(184, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(185, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(185, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(186, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(186, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(187, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(187, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(188, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(188, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(189, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(189, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(190, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(190, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(191, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(191, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(192, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(192, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(193, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(193, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(194, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(194, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(195, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(195, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(196)
    builder.add_next_value(196, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(196, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(197, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(197, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(198, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(198, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(199, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(199, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(200, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(200, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(201, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(201, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(202, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(202, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(203, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(203, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(204, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(204, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(205, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(205, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(206, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(206, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(207, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(207, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(208, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(208, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(209, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(209, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(210, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(210, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(211, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(211, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(212, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(212, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(213, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(213, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(214, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(214, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(215, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(215, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(216, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(216, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(217, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(217, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(218, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(218, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(219, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(219, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(220, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(220, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(221, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(221, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(222, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(222, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(223, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(223, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(224, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(224, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(225, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(225, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(226, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(226, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(227, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(227, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(228, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(228, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(229, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(229, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(230, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(230, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(231, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(231, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(232, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(232, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(233, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(233, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(234, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(234, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(235, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(235, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(236, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(236, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(237, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(237, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(238, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(238, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(239, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(239, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(240, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(240, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(241, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(241, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(242, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(242, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(243, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(243, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(244, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(244, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(245, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(245, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(246, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(246, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(247, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(247, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(248, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(248, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(249, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(249, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(250, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(250, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(251, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(251, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(252, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(252, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(253, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(253, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(254, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(254, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(255, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(255, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(256, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(256, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(257, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(257, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(258, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(258, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(259)
    builder.add_next_value(259, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(259, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(260, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(260, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(261, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(261, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(262, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(262, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(263, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(263, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(264, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(264, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(265, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(265, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(266, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(266, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(267, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(267, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(268, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(268, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(269, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(269, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(270, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(270, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(271, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(271, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(272, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(272, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(273, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(273, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(274, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(274, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(275, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(275, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(276, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(276, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(277, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(277, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(278, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(278, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(279, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(279, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(280, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(280, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(281, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(281, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(282, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(282, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(283, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(283, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(284, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(284, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(285, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(285, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(286, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(286, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(287, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(287, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(288, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(288, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(289, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(289, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(290, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(290, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(291, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(291, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(292, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(292, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(293, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(293, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(294, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(294, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(295, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(295, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(296, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(296, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(297, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(297, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(298, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(298, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(299, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(299, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(300, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(300, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(301, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(301, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(302, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(302, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(303, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(303, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(304, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(304, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(305, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(305, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(306, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(306, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(307, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(307, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(308, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(308, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(309, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(309, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(310, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(310, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(311, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(311, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(312, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(312, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(313, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(313, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(314, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(314, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(315, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(315, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(316, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(316, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(317, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(317, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(318, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(318, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(319, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(319, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(320, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(320, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(321, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(321, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(322)
    builder.add_next_value(322, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(322, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(323, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(323, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(324, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(324, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(325, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(325, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(326, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(326, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(327, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(327, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(328, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(328, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(329, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(329, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(330, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(330, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(331, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(331, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(332, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(332, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(333, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(333, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(334, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(334, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(335, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(335, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(336, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(336, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(337, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(337, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(338, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(338, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(339, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(339, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(340, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(340, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(341, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(341, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(342, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(342, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(343, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(343, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(344, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(344, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(345, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(345, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(346, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(346, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(347, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(347, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(348, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(348, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(349, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(349, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(350, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(350, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(351, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(351, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(352, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(352, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(353, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(353, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(354, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(354, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(355, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(355, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(356, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(356, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(357, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(357, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(358, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(358, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(359, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(359, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(360, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(360, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(361, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(361, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(362, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(362, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(363, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(363, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(364, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(364, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(365, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(365, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(366, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(366, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(367, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(367, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(368, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(368, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(369, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(369, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(370, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(370, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(371, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(371, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(372, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(372, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(373, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(373, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(374, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(374, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(375, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(375, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(376, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(376, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(377, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(377, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(378, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(378, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(379, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(379, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(380, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(380, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(381, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(381, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(382, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(382, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(383, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(383, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(384, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(384, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(385)
    builder.add_next_value(385, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(385, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(386, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(386, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(387, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(387, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(388, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(388, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(389, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(389, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(390, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(390, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(391, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(391, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(392, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(392, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(393, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(393, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(394, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(394, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(395, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(395, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(396, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(396, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(397, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(397, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(398, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(398, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(399, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(399, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(400, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(400, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(401, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(401, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(402, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(402, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(403, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(403, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(404, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(404, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(405, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(405, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(406, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(406, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(407, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(407, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(408, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(408, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(409, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(409, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(410, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(410, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(411, 1, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(411, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(412, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(412, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(413, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(413, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(414, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(414, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(415, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(415, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(416, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(416, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(417, 8, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(417, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(418, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(418, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(419, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(419, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(420, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(420, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(421, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(421, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(422, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(422, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(423, 9, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(423, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(424, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(424, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(425, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(425, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(426, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(426, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(427, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(427, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(428, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(428, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(429, 10, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(429, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(430, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(430, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(431, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(431, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(432, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(432, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(433, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(433, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(434, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(434, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(435, 11, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(435, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(436, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(436, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(437, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(437, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(438, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(438, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(439, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(439, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(440, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(440, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(441, 12, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(441, 19, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(442, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(442, 14, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(443, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(443, 15, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(444, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(444, 16, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(445, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(445, 17, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(446, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(446, 18, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(447, 13, stormpy.Rational(1) / stormpy.Rational(2))
    builder.add_next_value(447, 19, stormpy.Rational(1) / stormpy.Rational(2))

    builder.new_row_group(448)
    builder.add_next_value(448, 14, stormpy.Rational(1))

    builder.new_row_group(449)
    builder.add_next_value(449, 15, stormpy.Rational(1))

    builder.new_row_group(450)
    builder.add_next_value(450, 16, stormpy.Rational(1))

    builder.new_row_group(451)
    builder.add_next_value(451, 17, stormpy.Rational(1))

    builder.new_row_group(452)
    builder.add_next_value(452, 18, stormpy.Rational(1))

    builder.new_row_group(453)
    builder.add_next_value(453, 19, stormpy.Rational(1))

    transition_matrix = builder.build()
    state_labeling = initial_mod.labeling
    components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix, state_labeling=state_labeling)
    mdp = stormpy.storage.SparseExactMdp(components)
    initial_model = mdp
    return initial_model


if __name__ == '__main__':
    part_path = sys.argv[1]
    folder_file = part_path.split('_', 1)
    subfolder_file = folder_file[1].split('_', 1)
    path = files._path(folder_file[0], subfolder_file[0], subfolder_file[1] + '.nm')
    print(path)
    initial_prism_program = stormpy.parse_prism_program(path)
    initial_model = stormpy.build_model(initial_prism_program)
    print("No of state: " + str(len(initial_model.states)))
    tar = 0
    for state in initial_model.states:
        for action in state.actions:
            for tran in action.transitions:
                tar += 1
                print("State: " + str(state.id) + ", Action= " + str(action.id) + ", tran= " + str(
                    tran.column) + ", " + str(tran.value()))

    write_model_for_exact(initial_model, subfolder_file)

    # initial_model = build_model_manually_synthesis(initial_model)
    # initial_model = build_model_manually_synthesis0(initial_model)
    # initial_model = build_model_manually_synthesis0_1(initial_model)
    # initial_model = build_model_manually_synthesis_reduced(initial_model)
    # initial_model = build_model_manually_conformance5int(initial_model)
    initial_model = build_model_manually_synthesis_all(initial_model)

    print("Total transitions: " + str(tar))

    lab = initial_model.labeling
    for state in initial_model.states:
        print(lab.get_labels_of_state(state.id))

    parser = Lark(turtle_grammar)
    formula = sys.argv[2]
    parsed_formula_initial = parser.parse(formula)
    s = Solver()

    # x = Int('x')
    # y = Int('y')
    # # y = x
    # # for i in range(3):
    # #     y = y * x
    #
    # s.add(y == 16)
    # s.add(x>0)
    # startt = time.process_time()
    # m = s.check()
    # print("time = " + str(time.process_time() - startt))
    # n = s.model()
    # q = Solver()
    #
    # x = Bool('x')
    # y = Bool('y')
    # z = Bool('z')
    # q.add(And(And(x), Or(y, z)))
    # startt = time.process_time()
    # m = q.check()
    # print("time = " + str(time.process_time() - startt))

    # # s.add(And(Or(x==0, y==1), Or(x==1, y==0)))
    # # s.add()
    # m = s.check()
    # n = q.model()

    f_pointer = open("encoding.txt", "w")
    result = main_smt_encoding(initial_model, parsed_formula_initial, formula)
    f_pointer.close()
    print(result)
