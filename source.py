import csv
import itertools
import sys

import stormpy
import files
from lark import Lark, Token, Tree
from z3 import *

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
list_of_z3_variables = []
csvData = []


def example_schedulers_01():
    path = files.mdp_exampleand
    formula_str = "Pmin=? [F \"two\"]"

    program = stormpy.parse_prism_program(path)
    formulas = stormpy.parse_properties_for_prism_program(formula_str, program)
    model = stormpy.build_model(program)
    initial_state = model.initial_states[0]
    assert initial_state == 0
    result = stormpy.model_checking(model, formulas[0], extract_scheduler=True)
    assert result.has_scheduler
    scheduler = result.scheduler
    print(scheduler)
    assert scheduler.memoryless
    assert scheduler.deterministic

    for state in model.states:
        choice = scheduler.get_choice(state)
        action = choice.get_deterministic_choice()
        print("In state {} choose action {}".format(state, action))


def try_z3():
    x1 = Int('x1')
    y = Int('y')
    y1 = Int('y1')
    z = Bool('z')
    z1 = Bool('z1')
    s = Solver()
    equation = Or()
    equation.children = [z == True, z1 == True]
    s.add(Or(z))
    # s.add(Or(z))
    t1 = s.check()
    m = s.model()
    s.add(And(z1 == True, Or(z), And(z, z1, )))
    # s.add(y == 2)
    # s.add(x1 + y == 5)
    t = s.check()
    print("Hi")


def SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n):
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    phi2 = formula_duplicate.children[0].children[1]
    index_of_phi2 = list_of_subformula.index(phi2)
    # s112 = Semantics(model, phi1, combined_list_of_states, n)
    # s212 = Semantics(model, phi2, combined_list_of_states, n)
    result_string = 'A(' + Semantics(model, phi1, combined_list_of_states, n) + ' ' + Semantics(model, phi2, combined_list_of_states, n) + ')'
    result_string = 'A(' + result_string + ' '
    sum_of_loop1 = 'A('
    sum_of_loop2 = 'A('
    index_of_phi = list_of_subformula.index(formula_duplicate)
    for li in combined_list_of_states:
        first_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '=1' + ' holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ')'
        second_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '=0' + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '))'
        final_or1 = 'V(' + first_and1 + ' ' + second_and1 + ')'
        sum_of_loop1 += final_or1 + ' '
        first_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '=1' + ' holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ')'
        second_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '=0' + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '))'
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

    dict_of_acts = dict()
    dict_of_acts_tran = dict()
    for state in model.states:
        list_of_act = []
        for action in state.actions:
            list_of_tran = []
            list_of_act.append(action.id)
            for tran in action.transitions:
                # list_of_tran.append({tran.column: tran.value()})
                list_of_tran.append(str(tran.column) + ' ' + str(tran.value()))
            dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
        dict_of_acts[state.id] = list_of_act
    # result_string = 'A(' + result_string + ' '

    for li in combined_list_of_states:
        result_string = 'A(' + result_string + ' '
        first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
        if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
            list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
        second_implies = 'I(A(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ') N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
            index_of_phi2) + ')) ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=0)'
        result_string += first_implies + ' ' + second_implies + ')'
        combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
        for ca in combined_acts:
            implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ') A(a_' + str(li[0]) + '=' + str(ca[0]) + ' a_' + str(li[1]) + '=' + str(ca[1]) + '))'
            if 'a_' + str(li[0]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[0]))
            if 'a_' + str(li[1]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[1]))

            implies_antecedent_and1 = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
            combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])], dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
            first = False
            if len(combined_succ) == 1:
                first = True
            prod_left = 'P('
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                if first:
                    prod_left = 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi) + ') '
                else:
                    prod_left += 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi) + ') '
                if 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi) not in list_of_z3_variables:
                    list_of_z3_variables.append('prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi))
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
                    prod_right_or = 'V(holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2) + ' g(d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                        index_of_phi2) + ' d_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2) + ')) '
                else:
                    prod_right_or += 'V(holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2) + ' g(d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                        index_of_phi2) + ' d_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2) + ')) '
                if 'holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append('holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2))
                if 'd_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append('d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
                if 'd_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append('d_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2))
            if first:
                implies_antecedent_and2 += prod_right_or[0:len(prod_right_or) - 1] + ')'
            else:
                implies_antecedent_and2 += prod_right_or[0:len(prod_right_or) - 1] + '))'
            implies_antecedent = 'I(' + implies_antecedent_and1 + ' ' + implies_antecedent_and2 + ')'
            result_string = 'A(' + result_string + ' I(' + implies_precedent + ' ' + implies_antecedent + '))'
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
        result_string = 'A(' + Semantics(model, phi1, combined_list_of_states, n) + ' ' + Semantics(model, phi2, combined_list_of_states, n) + ')'
        result_string = 'A(' + result_string + ' '
        sum_of_loop1 = 'A('
        sum_of_loop2 = 'A('
        for li in combined_list_of_states:
            first_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '=1' + ' holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ')'
            second_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '=0' + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + '))'
            final_or1 = 'V(' + first_and1 + ' ' + second_and1 + ')'
            sum_of_loop1 += final_or1 + ' '
            first_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '=1' + ' holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ')'
            second_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '=0' + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
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
            first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
            second_implies = 'I(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ')' + ' prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi) + '=0)'
            result_string += first_implies + ' ' + second_implies + ')'
        result_string += ')'

    elif k1 == 0:
        left, k_1, k_2, right = formula_duplicate.children
        par = copy.deepcopy(k_2)
        par.value = str(
            int(k_2.value) - 1)  # k2.value will have changed value but it won't show up in the formula tree, hence it'll appear to be the same formula as formula_duplicate
        formula_duplicate.children[2] = par  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2. Don't be confused!!
        list_of_subformula.append(formula_duplicate)
        index_of_replaced = len(list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
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
            first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
            second_implies = 'I(A(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ') N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ')) ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=0)'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            result_string += first_implies + ' ' + second_implies + ')'
            combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
            for ca in combined_acts:
                implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_of_phi2) + ') A(a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) + '=' + str(ca[0]) + ' a_s' + str(
                    combined_list_of_states.index(li)) + '_' + str(1) + '=' + str(ca[1]) + '))'
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(0))
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(1))

                implies_antecedent = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
                combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])], dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
                if len(combined_succ) == 1:
                    first = True
                prod = 'P('
                for cs in combined_succ:
                    if first:
                        prod = 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    else:
                        prod += 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    if 'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced) not in list_of_z3_variables:
                        list_of_z3_variables.append('prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced))
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
        formula_duplicate.children[1] = par1  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2 Don't be confused!!
        formula_duplicate.children[2] = par2
        list_of_subformula.append(formula_duplicate)
        index_of_replaced = len(list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
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
            first_implies = 'I(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ') ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi) + '=0)'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
            result_string += first_implies + ')'
            combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
            for ca in combined_acts:
                implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ' A(a_s' + str(combined_list_of_states.index(li)) + '_' + str(
                    0) + '=' + str(ca[0]) + ' a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) + '=' + str(ca[1]) + '))'
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(0))
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(1))

                implies_antecedent = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
                combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])], dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
                if len(combined_succ) == 1:
                    first = True
                prod = 'P('
                for cs in combined_succ:
                    if first:
                        prod = 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    else:
                        prod += 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    if 'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced) not in list_of_z3_variables:
                        list_of_z3_variables.append('prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced))
                if first:
                    implies_antecedent += prod[0:len(prod) - 1]
                    first = False
                else:
                    implies_antecedent += prod[0:len(prod) - 1] + ')'
                implies_antecedent += ')'

                result_string = 'A(' + result_string + ' I(' + implies_precedent + ' ' + implies_antecedent + '))'

    return result_string


def SemanticsNext(model, formula_duplicate, combined_list_of_states, n):
    result_string = ''
    phi1 = formula_duplicate.children[0].children[0]
    result_string = Semantics(model, phi1, combined_list_of_states, n)
    result_string = 'A(' + result_string + ' A('
    index_phi1 = list_of_subformula.index(phi1)
    for li in combined_list_of_states:
        pos_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '=1 holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ')'
        if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
        neg_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '=0 N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '))'
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
                # list_of_tran.append({tran.column: tran.value()})
                list_of_tran.append(str(tran.column) + ' ' + str(tran.value()))  # storing just transition values, not state it transitions to
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
            mul_clause = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + ' '
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
            combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])], dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))

            if len(combined_succ) == 1:
                first = True
            prod = 'P('
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                if first:
                    prod = 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_phi1) + ') '
                else:
                    prod += 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_phi1) + ') '
                if 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_phi1) not in list_of_z3_variables:
                    list_of_z3_variables.append('prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_phi1))
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


def Semantics(model, formula_duplicate, combined_list_of_states, n):
    result_string = ''
    if formula_duplicate.data == 'true':
        result_string += 'A('
        index_of_phi = list_of_subformula.index(formula_duplicate)
        for i in range(len(combined_list_of_states)):
            result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + ' '
            if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
        result_string = result_string[0: len(result_string) - 1] + ')'
    elif formula_duplicate.data == 'var':  # var handles the inside varname
        list_of_state_with_ap = []
        ap_name = formula_duplicate.children[0].children[0].value
        ap_state = formula_duplicate.children[0].children[1].value[1]
        labeling = model.labeling
        and_for_yes = 'A('
        and_for_no = 'A('
        index_of_phi = list_of_subformula.index(formula_duplicate)
        for state in model.states:
            if ap_name in labeling.get_labels_of_state(state.id):
                list_of_state_with_ap.append(state.id)
        for li in combined_list_of_states:
            if li[int(ap_state) - 1] in list_of_state_with_ap:
                and_for_yes += 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
            else:
                and_for_no += 'N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ') '
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
        and_for_yes = and_for_yes[0: len(and_for_yes) - 1] + ')'
        and_for_no = and_for_no[0: len(and_for_no) - 1] + ')'
        if and_for_yes.find('holds') == -1:
            result_string = and_for_no
        elif and_for_no.find('holds') == -1:
            result_string = and_for_yes
        else:
            result_string = 'A(' + and_for_yes + ' ' + and_for_no + ')'
    elif formula_duplicate.data == 'and_op':
        result_string = 'A(' + Semantics(model, formula_duplicate.children[0], combined_list_of_states, n) + ' ' + Semantics(model, formula_duplicate.children[1],
                                                                                                                             combined_list_of_states, n) + ')'
        sum_of_loop = 'A('
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        for li in combined_list_of_states:
            first_ands = "A(holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ' ' + 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_phi1) + ' ' + 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + ')'
            second_mix = "A(N(holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ') ' + 'V(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_phi1) + ') ' + 'N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + ')))'
            if "holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) not in list_of_z3_variables:
                list_of_z3_variables.append("holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi))
            if "holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append("holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
            if "holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append("holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2))
            sum_of_loop += 'V(' + first_ands + " " + second_mix + ') '
        sum_of_loop = sum_of_loop[0: len(sum_of_loop) - 1] + ')'
        result_string = 'A(' + result_string + ' ' + sum_of_loop + ') '
    elif formula_duplicate.data == 'neg_op':
        sem = Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        result_string = 'A(' + sem + ' A('
        for li in combined_list_of_states:
            result_string += 'X(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ' ' + 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ') '
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
        result_string = result_string[0:len(result_string) - 1] + '))'
    elif formula_duplicate.data == 'less_prob':
        result_string = 'A(' + Semantics(model, formula_duplicate.children[0], combined_list_of_states, n) + ' ' + Semantics(model, formula_duplicate.children[1],
                                                                                                                             combined_list_of_states, n) + ')'
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        result_string = 'A(' + result_string + ' A('
        for li in combined_list_of_states:
            and_less = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ' l(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ' prob_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + '))'
            and_great = 'A(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ') G(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_phi1) + ' prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + '))'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2))
            result_string += 'V(' + and_less + ' ' + and_great + ') '
        result_string = result_string[0:len(result_string) - 1] + '))'
    elif formula_duplicate.data == 'greater_prob':
        result_string = 'A(' + Semantics(model, formula_duplicate.children[0], combined_list_of_states, n) + ' ' + Semantics(model, formula_duplicate.children[1],
                                                                                                                             combined_list_of_states, n) + ')'
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        result_string = 'A(' + result_string + ' A('
        for li in combined_list_of_states:
            and_less = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ' g(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ' prob_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + '))'
            and_great = 'A(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ') L(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_phi1) + ' prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + '))'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2))
            result_string += 'V(' + and_less + ' ' + and_great + ') '
        result_string = result_string[0:len(result_string) - 1] + '))'
    elif formula_duplicate.data == 'calc_probability':
        child = formula_duplicate.children[0]
        if child.data == 'calc_next':
            result_string = SemanticsNext(model, formula_duplicate, combined_list_of_states, n)
        elif child.data == 'calc_until_unbounded':
            result_string = SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n)
        elif child.data == 'calc_until_bounded':
            result_string = SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)
    # elif formula_duplicate.data == 'calc_next':
    #     phi1 = formula_duplicate.children[0].children[0]
    #     result_string = Semantics(model, phi1, combined_list_of_states, n)
    #     result_string = 'A(' + result_string + ' A('
    #     index_phi1 = list_of_subformula.index(phi1)
    #     for li in combined_list_of_states:
    #         pos_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '=1 holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ')'
    #         if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
    #             list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
    #         if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
    #             list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
    #         neg_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '=0 N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '))'
    #         result_string += 'V(' + pos_and + ' ' + neg_and + ') '
    #     result_string = result_string[0:len(result_string) - 1] + '))'
    #     dict_of_acts = dict()
    #     dict_of_acts_tran = dict()
    #     for state in model.states:
    #         list_of_act = []
    #         for action in state.actions:
    #             list_of_tran = []
    #             list_of_act.append(action.id)
    #             for tran in action.transitions:
    #                 # list_of_tran.append({tran.column: tran.value()})
    #                 list_of_tran.append(str(tran.column) + ' ' + str(tran.value()))  # storing just transition values, not state it transitions to
    #             dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
    #         dict_of_acts[state.id] = list_of_act
    #     result_string = 'A(' + result_string + ' '
    #     for li in combined_list_of_states:
    #         combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
    #         for ca in combined_acts:
    #             implies_precedent = 'A(a_' + str(li[0]) + '=' + str(ca[0]) + ' a_' + str(li[1]) + '=' + str(ca[1]) + ')'
    #             if 'a_' + str(li[0]) not in list_of_z3_variables:
    #                 list_of_z3_variables.append('a_' + str(li[0]))
    #             if 'a_' + str(li[1]) not in list_of_z3_variables:
    #                 list_of_z3_variables.append('a_' + str(li[1]))
    #             mul_clause = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + ' '
    #             if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
    #                 list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
    #             combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])], dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
    #
    #             if len(combined_succ) == 1:
    #                 first = True
    #             prod = 'P('
    #             for cs in combined_succ:
    #                 space_in0 = cs[0].find(' ')
    #                 space_in1 = cs[1].find(' ')
    #                 if first:
    #                     prod = 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
    #                         index_phi1) + ') '
    #                 else:
    #                     prod += 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
    #                         index_phi1) + ') '
    #                 if 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_phi1) not in list_of_z3_variables:
    #                     list_of_z3_variables.append('prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_phi1))
    #             if first:
    #                 mul_clause += prod[0:len(prod) - 1] + ')'
    #                 first = False
    #             else:
    #                 mul_clause += prod[0:len(prod) - 1] + '))'
    #             # implies_antecedent = '(' + mul_clause + ')'
    #             implies_antecedent = mul_clause
    #             state_act_clause = 'I(' + implies_precedent + ' ' + implies_antecedent + ')'
    #             result_string += state_act_clause + ' '
    #     result_string = result_string[0:len(result_string) - 1] + ')'

    elif formula_duplicate.data == 'calc_until_unbounded':
        result_string = SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n)
    elif formula_duplicate.data == 'calc_until_bounded':
        result_string = SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)
    elif formula_duplicate.data == 'const':
        c = formula_duplicate.children[0].value
        result_string = 'A('
        for li in combined_list_of_states:
            result_string += 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + '=' + c + ' '
            if ('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate))) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
        result_string = result_string[0:len(result_string) - 1] + ')'
    elif formula_duplicate.data in ['add_prob', 'minus_prob', 'mul_prob']:
        left = formula_duplicate.children[0]
        index_left = list_of_subformula.index(left)
        right = formula_duplicate.children[1]
        index_right = list_of_subformula.index(right)
        result_string = 'A(' + Semantics(model, left, combined_list_of_states, n) + ' ' + Semantics(model, right, combined_list_of_states, n) + ')'
        result_string = 'A(' + result_string + ' A('
        op = ''
        for li in combined_list_of_states:
            if formula_duplicate.data == 'add_prob':
                op = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + '=P(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_left) + ' prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right) + ')'
            elif formula_duplicate.data == 'minus_prob':
                op = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + '=S(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_left) + ' prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right) + ')'
            elif formula_duplicate.data == 'mul_prob':
                op = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + '=M(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_left) + ' prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right) + ')'
            result_string += op + ' '
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
        result_string = result_string[0:len(result_string)] + '))'

    return result_string


def Truth(model, formula_initial, combined_list_of_states, n):
    list_of_AV = []  # will have the OR,AND according to the quantifier in that index in the formula

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
    result_string = ""
    if n == 2:
        if list_of_AV[0] == 'V':
            result_string += ' V('
        else:
            result_string += ' A('
        first = True
        for i in range(len(combined_list_of_states)):
            if first or combined_list_of_states[i - 1][0] == combined_list_of_states[i][0] - 1:
                if list_of_AV[1] == 'V':
                    result_string += "V(holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " "
                else:
                    result_string += "A(holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " "
                first = False
            elif ((i + 1) == len(combined_list_of_states)) or combined_list_of_states[i][0] == combined_list_of_states[i + 1][0] - 1:
                result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + ") "
            else:
                if list_of_AV[1] == 'V':
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " "
            if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
        result_string = result_string[0:len(result_string) - 1] + ')'
    return result_string


def toSMT2Benchmark(f, status="unknown", name="benchmark", logic=""):
    v = (Ast * 0)()
    return Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast())


def check(F):  # this will take the string F, convert it to z3 compatible equation and return the result of smt checking, True if sat
    list_of_reals = []
    listOfReals = []
    list_of_bools = []
    listOfBools = []
    list_of_ints = []
    listOfInts = []

    for name in list_of_z3_variables:
        if name[0] == 'h':
            list_of_bools.append(name)
            listOfBools.append(Bool(name))
        elif name[0] in ['p', 'd']:
            list_of_reals.append(name)
            listOfReals.append(Real(name))
        elif name[0] == 'a':
            list_of_ints.append(name)
            listOfInts.append(Int(name))
        else:
            print(name)
    total_eqn = None
    i = 0
    operator = []
    operands = []
    open_paran = 0
    close_paran = 0
    s_in_op = False
    n_in_op = False
    le = len(F)
    while i < len(F):
        ch = F[i]
        if F[i] in ['A', 'V', 'I', 'N', 'X', 'E', 'P', 'M', 'S', 'L', 'l', 'G', 'g']:
            operator.append(F[i])
            i += 1
        elif F[i] == '(':
            open_paran += 1
            operands.append(' ')
            i += 1
        elif F[i] in ['a', 'h', 'p', 'd'] or F[i].isdigit():
            s_in_op = True
            op_space_index = F.find(' ', i)
            op_brac_index = F.find(')', i)
            if (op_space_index < op_brac_index and op_space_index != -1) or op_brac_index == -1:
                operands.append(F[i:op_space_index])
                i = op_space_index
            else:  # if (op_space_index > op_brac_index and op_brac_index != -1) or op_space_index == -1:
                operands.append((F[i:op_brac_index]))
                i = op_brac_index
        elif F[i] == ')':
            close_paran += 1
            if operator[open_paran - close_paran] in ['V', 'A', 'I', 'X', 'N', 'X', 'E', 'P', 'M', 'S', 'L', 'l', 'G', 'g']:
                equation = None
                if s_in_op:
                    ran_list = []
                    k = 0
                    for k in range(len(operands) - 1, 0, -1):
                        if type(operands[k]) == str and operands[k] == ' ':
                            break
                    k += 1
                    while k < len(operands):
                        if type(operands[k]) == str and operands[k] != ' ':
                            if operands[k][0] == 'a':
                                eq_index = operands[k].find('=', 0)
                                num = int(operands[k][eq_index + 1:])
                                name = operands[k][0:eq_index]
                                ran_list.append(listOfInts[list_of_ints.index(name)] == num)
                                operands.pop(k)
                            elif operands[k][0] == 'h':
                                ran_list.append(listOfBools[list_of_bools.index(operands[k])])
                                operands.pop(k)
                            elif operands[k][0] == 'd':
                                ran_list.append(listOfReals[list_of_reals.index(operands[k])])
                                operands.pop(k)
                            elif operands[k][0] == 'p':
                                eq_index = operands[k].find('=', 0)
                                if eq_index == -1:
                                    name = operands[k]
                                    ran_list.append(listOfReals[list_of_reals.index(name)])
                                else:
                                    num = float(operands[k][eq_index + 1:])
                                    name = operands[k][0:eq_index]
                                    ran_list.append(listOfReals[list_of_reals.index(name)] == num)
                                operands.pop(k)
                            elif operands[k][0].isdigit():
                                num = float(operands[k])
                                ran_list.append(num)
                                operands.pop(k)
                        else:
                            ran_list.append(operands[k])
                            operands.pop(k)
                            # k += 1
                    if operator[open_paran - close_paran] == 'V':
                        equation = Or([par for par in ran_list])
                    elif operator[open_paran - close_paran] == 'A':
                        equation = And([par for par in ran_list])
                    elif operator[open_paran - close_paran] == 'N':
                        equation = Not(ran_list[0])
                        n_in_op = True
                    elif operator[open_paran - close_paran] == 'I':
                        equation = Implies(ran_list[0], ran_list[1])
                    elif operator[open_paran - close_paran] == 'X':
                        equation = Xor(ran_list[0], ran_list[1])
                    elif operator[open_paran - close_paran] == 'M':
                        for lk in ran_list:
                            if equation is None:
                                equation = lk
                            else:
                                equation *= lk
                    elif operator[open_paran - close_paran] == 'E':
                        equation = ran_list[0] == ran_list[1]
                    elif operator[open_paran - close_paran] == 'P':
                        for lk in ran_list:
                            if equation is None:
                                equation = lk
                            else:
                                equation += lk
                    elif operator[open_paran - close_paran] == 'L':
                        equation = ran_list[0] <= ran_list[1]
                    elif operator[open_paran - close_paran] == 'l':
                        equation = ran_list[0] < ran_list[1]
                    elif operator[open_paran - close_paran] == 'G':
                        equation = ran_list[0] >= ran_list[1]
                    elif operator[open_paran - close_paran] == 'g':
                        equation = ran_list[0] > ran_list[1]
                    operands.pop()
                    operands.append(equation)
                    operator.pop()
                    flag = False
                    for fg in operands:
                        if type(fg) == str and fg != ' ':
                            flag = True
                            break
                    if flag:
                        s_in_op = True
                    else:
                        s_in_op = False
                else:  # not s_in_op and n_in_op
                    ls = len(operands) - 1
                    while ls >= 0:
                        if type(operands[ls]) == str and operands[ls] == ' ':
                            break
                        ls -= 1
                    po = ls + 1
                    new_ops = []
                    while po < len(operands):
                        new_ops.append(operands[po])
                        operands.pop(po)
                    if operator[open_paran - close_paran] == 'V':
                        equation = Or([par for par in new_ops])
                    elif operator[open_paran - close_paran] == 'A':
                        equation = And([par for par in new_ops])
                    elif operator[open_paran - close_paran] == 'N':
                        equation = Not(new_ops.pop())
                        n_in_op = True
                    elif operator[open_paran - close_paran] == 'I':
                        equation = Implies(new_ops[0], new_ops[1])
                    elif operator[open_paran - close_paran] == 'X':
                        equation = Xor(new_ops[0], new_ops[1])
                    operands.pop()
                    operands.append(equation)
                    operator.pop()
            i += 1
        elif F[i] == ' ':
            i += 1
    if close_paran == open_paran:
        print('True')
    csvData.append(toSMT2Benchmark(equation, logic="QF_LIA"))
    s = Solver()
    s.add(equation)
    # csvData.append(equation)
    t = s.check()
    if t == sat:
        m = s.model()
        li_h = dict()
        for li in m:
            if li.name()[0] == 'h':
                li_h[li.name()] = m[li]
        li_p = dict()
        for li in m:
            if li.name()[0] == 'p':
                li_p[li.name()] = m[li]
        li_a = dict()
        for li in m:
            if li.name()[0] == 'a':
                li_a[li.name()] = m[li]
        csvData.append([m])
    if t.r == 1:
        return True
    elif t.r == -1:
        return False


def add_to_subformula_list(formula_phi):  # add as you go any new subformula part as needed
    if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist', 'forall']:
        formula_phi = formula_phi.children[1]
        add_to_subformula_list(formula_phi)
    elif formula_phi.data in ['and_op', 'less_prob', 'greater_prob', 'add_prob', 'minus_prob', 'mul_prob', 'calc_until_unbounded', 'equal_prob']:
        list_of_subformula.append(formula_phi)
        left_child = formula_phi.children[0]
        add_to_subformula_list(left_child)
        right_child = formula_phi.children[1]
        add_to_subformula_list(right_child)
    elif formula_phi.data in ['var', 'true', 'const']:
        list_of_subformula.append(formula_phi)
    elif formula_phi.data in ['calc_next', 'neg_op']:
        list_of_subformula.append(formula_phi)
        add_to_subformula_list(formula_phi.children[0])
    elif formula_phi.data in ['calc_probability']:
        list_of_subformula.append(formula_phi)
        add_to_subformula_list(formula_phi.children[0])
    elif formula_phi.data in ['calc_until_bounded']:
        list_of_subformula.append(formula_phi)
        left_child = formula_phi.children[0]
        add_to_subformula_list(left_child)
        right_child = formula_phi.children[3]
        add_to_subformula_list(right_child)


def main_smt_encoding(model, formula_initial, formula):
    first_o = True
    list_of_states = []
    F = 'A('

    for state in model.states:
        first_i = True
        sa = 'V('
        for action in state.actions:
            act = "a_" + str(state.id) + "=" + str(action.id)  # a1 means action for state 1
            if "a_" + str(state.id) not in list_of_z3_variables:
                list_of_z3_variables.append("a_" + str(state.id))
            if first_i:
                sa += act
                first_i = False
            else:
                sa += ' ' + act
        sa += ')'
        if first_o:
            F += sa
            first_o = False
        else:
            F += " " + sa
    F += ')'
    n = 0
    formula_duplicate = formula_initial
    while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist', 'forall']:
            n += 1
            formula_duplicate = formula_duplicate.children[1]
    for state in model.states:
        list_of_states.append(state.id)
    combined_list_of_states = list(itertools.product(list_of_states, repeat=n))
    if formula_initial.data == 'exist_scheduler':
        add_to_subformula_list(formula_initial)
        truth_result = Truth(model, formula_initial, combined_list_of_states, n)
        semantics_result = Semantics(model, formula_duplicate, combined_list_of_states, n)
        F = "A(" + F + " " + semantics_result + " " + truth_result + ")"
        csvData.append([F])
        if check(F):
            return True
        else:
            return False

    elif formula_initial.data == 'forall_scheduler':
        new_formula = ''
        i = 0
        first = True
        while i < len(formula):
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
                    new_formula += '~'
                    first = False
                new_formula += formula[i]
                i += 1
        new_parsed_formula = parser.parse(new_formula)
        formula_duplicate = new_parsed_formula
        n = 0
        while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
            if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
                formula_duplicate = formula_duplicate.children[1]
            elif formula_duplicate.data in ['exist', 'forall']:
                n += 1
                formula_duplicate = formula_duplicate.children[1]
        add_to_subformula_list(new_parsed_formula)
        semantics_result = Semantics(model, formula_duplicate, combined_list_of_states, n)
        truth_result = Truth(model, new_parsed_formula, combined_list_of_states, n)
        F = 'A(' + F + ' ' + semantics_result + ' ' + truth_result + ')'
        csvData.append([F])
        if check(F):
            return False
        else:
            return True


if __name__ == '__main__':
    part_path = sys.argv[1]
    folder_file = part_path.split('_', 1)
    path = files._path(folder_file[0], folder_file[1] + ".nm")
    print(path)
    initial_prism_program = stormpy.parse_prism_program(path)
    initial_model = stormpy.build_model(initial_prism_program)

    # try_z3()

    parser = Lark(turtle_grammar)
    formula = sys.argv[2]
    parsed_formula_initial = parser.parse(formula)
    with open('resultdiffprivy.csv', 'w') as csvFile:
        writer = csv.writer(csvFile, delimiter=',')
        row = [formula]
        csvData.append(row)
        row = ['-----------------------------------------------------']
        csvData.append(row)
        result = main_smt_encoding(initial_model, parsed_formula_initial, formula)
        writer.writerows(csvData)
    csvFile.close()
    print(result)

# A = And, V = Or,  X = Xor,  I = Implies, G = greater than equal,  g = greater,  M = multiplication,  P = Addition, S = subtraction, E = equal, L = less than equal, l = less

# mdp_example_and "ES sh . E s1 . E s2 . ( one(s1) & two(s2) )" s1 and s2 are dtmcs extended by using scheduler sh on the mdp example_and.nm
# mdp_example_neg_const "ES sh . E s1 . E s2 . (P(X ( one(s1) & two(s2) )) < 0.5)"
# mdp_example_neg_const "ES sh . E s1 . E s2 . ~one(s1)"
# mdp_example_neg_const "ES sh . A s1 . E s2 . (P(X one(s1)) < 0.5)"
# mdp_example_neg_const "ES sh . E s1 . E s2 . (P( one(s1) U[1,3] two(s2)) < 3)"

# mdp_data "AS sh . A s1 . A s1 . (P( true U bcy(s1)) > 0)
