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
          | "(" start "U[NUM , NUM]" start ")"-> calc_until_bounded
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
    s.add(And(Or(3 * x1 == y * y1, x1 == 3), Not(z), z1 == True, And(z, z1)))
    s.add(y == 2)
    s.add(x1 + y == 5)
    t = s.check()
    print("Hi")


def SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n):
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = formula_duplicate.index(phi1)
    phi2 = formula_duplicate.children[0].children[1]
    index_of_phi2 = list_of_subformula.index(phi2)
    result_string = 'A(' + Semantics(model, phi1, combined_list_of_states, n) + ' ' + Semantics(model, phi2, combined_list_of_states, n) + ')'
    result_string = 'A(' + result_string + ' '
    sum_of_loop1 = 'A('
    sum_of_loop2 = 'A('
    for li in combined_list_of_states:
        first_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '=1' + ', holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ')'
        second_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '=0' + ', Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '))'
        final_or1 = 'Or(' + first_and1 + ' ' + second_and1
        sum_of_loop1 += final_or1 + ' '
        first_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '=1' + ', holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ')'
        second_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '=0' + ', Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '))'
        final_or2 = 'Or(' + first_and2 + ' ' + second_and2
        sum_of_loop2 += final_or2 + ' '
        if "prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append("prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
        if "prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
            list_of_z3_variables.append("prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
    sum_of_loop1 += ')'
    sum_of_loop2 += ')'
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
                list_of_tran.append(tran.value())
            dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
        dict_of_acts[state.id] = list_of_act
    result_string = 'A(' + result_string + ' '

    for li in combined_list_of_states:
        result_string = 'A(' + result_string + ' '
        first_implies = 'Implies(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
            list_of_subformula.index(formula_duplicate)) + ' = 1'
        if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
            list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
        second_implies = 'Implies(A(Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ') Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
            index_of_phi2) + ')) ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + '=0)'
        result_string += first_implies + ' ' + second_implies
        combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
        for ca in combined_acts:
            implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ' Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ') A(a_' + str(combined_list_of_states.index(li)) + '_' + str(0) + ' = ' + str(ca[0]) + ', a_' + str(
                combined_list_of_states.index(li)) + '_' + str(1) + ' = ' + str(ca[1]) + '))'
            if 'a_' + str(combined_list_of_states.index(li)) + '_' + str(0) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(combined_list_of_states.index(li)) + '_' + str(0))
            if 'a_' + str(combined_list_of_states.index(li)) + '_' + str(1) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(combined_list_of_states.index(li)) + '_' + str(1))

            mul_clause = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + ' = A('
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
            combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])], dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
            first = True
            prod_left = ''
            for cs in combined_succ:
                if first:
                    prod_left = '(' + str(cs[0]) + ' * ' + str(cs[1]) + ' * ' + 'prob_s' + str(combined_succ.index(cs)) + '_' + str(
                        list_of_subformula.index(formula_duplicate)) + ')'
                    first = False
                else:
                    prod_left += '+ (' + str(cs[0]) + ' * ' + str(cs[1]) + ' * ' + 'prob_s' + str(combined_succ.index(cs)) + '_' + str(
                        list_of_subformula.index(formula_duplicate)) + ')'
                if 'prob_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                    list_of_z3_variables.append('prob_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(formula_duplicate)))
            mul_clause += prod_left + ', '
            prod_right = 'Implies((prob_' + str(combined_list_of_states.index(li)) + '_' + str(list_of_subformula.index(formula_duplicate)) + ' > 0) '
            prod_right_or = 'Or('
            for cs in combined_succ:
                prod_right_or += 'Or(holds_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi2)) + ' (d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_of_phi2) + ' > d_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi2)) + ')) '
                if 'holds_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi2)) not in list_of_z3_variables:
                    list_of_z3_variables.append('holds_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi2)))
                if 'd_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append('d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
                if 'd_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi2)) not in list_of_z3_variables:
                    list_of_z3_variables.append('d_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi2)))
            prod_right_or += ')'
            prod_right += prod_right_or + ')'
            mul_clause += prod_right + ')'
            result_string = 'A(' + result_string + ', ' + mul_clause
    return result_string


def SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n):
    result_string = ''
    return result_string


def Semantics(model, formula_duplicate, combined_list_of_states, n):
    result_string = ''
    if formula_duplicate.data == 'true':
        result_string += 'A('
        first = True
        index_of_phi = list_of_subformula.index(formula_duplicate)
        for i in range(len(combined_list_of_states)):
            if first:
                result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi)
                if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                    list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
                first = False
            else:
                result_string += ",holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi)
                if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                    list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
        result_string += ')'
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
                if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                    list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
            else:
                and_for_no += 'Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ') '
                if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                    list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
        and_for_yes += ')'
        and_for_no += ')'
        result_string = 'A(' + and_for_yes + and_for_no + ')'
    elif formula_duplicate.data == 'and_op':
        result_string = 'A(' + Semantics(model, formula_duplicate.children[0], combined_list_of_states, n) + Semantics(model, formula_duplicate.children[1],
                                                                                                                       combined_list_of_states, n) + ')'
        sum_of_loop = 'A('
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        for li in combined_list_of_states:
            first_ands = "A(holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ' ' + 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_phi1) + ' ' + 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + ')'
            if "holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) not in list_of_z3_variables:
                list_of_z3_variables.append("holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi))
            if "holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append("holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
            if "holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append("holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2))
            second_mix = "A(Not(holds_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ') ' + 'V(Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_phi1) + ') ' + 'Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + ')))'
            sum_of_loop += 'V(' + first_ands + " " + second_mix + ') '
        sum_of_loop += ')'
        result_string = 'A(' + result_string + ' ' + sum_of_loop + ') '
    elif formula_duplicate.data == 'neg_op':
        sem = Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        result_string = 'A(' + sem + 'A('
        for li in combined_list_of_states:
            result_string += 'Xor(' + 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ', ' + 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_phi1) + ') '
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
        result_string += '))'
    elif formula_duplicate.data == 'less_prob':
        result_string = 'A(' + Semantics(model, formula_duplicate.children[0], combined_list_of_states, n) + Semantics(model, formula_duplicate.children[1],
                                                                                                                       combined_list_of_states, n) + ')'
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        result_string = 'A(' + result_string + ' A('
        for li in combined_list_of_states:
            and_less = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + ', prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ' < prob_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + ')'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2))
            and_great = 'A(Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi) + '), prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_phi1) + ' >= prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2) + ')'
            result_string += 'V(' + and_less + ', ' + and_great + ')'
        result_string += '))'
    elif formula_duplicate.data == 'calc_probability':
        child = formula_duplicate.children[0]
        if child.data == 'calc_next':
            result_string = Semantics(model, child, combined_list_of_states, n)
        elif child.data == 'calc_until_unbounded':
            result_string = Semantics(model, child, combined_list_of_states, n)
        elif child.data == 'calc_until_bounded':
            result_string = Semantics(model, child, combined_list_of_states, n)
    elif formula_duplicate.data == 'calc_next':
        phi1 = formula_duplicate.children[0]
        result_string = Semantics(model, phi1, combined_list_of_states, n)
        result_string = 'A(' + result_string + ' A('
        index_phi1 = list_of_subformula.index(phi1)
        for li in combined_list_of_states:
            pos_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ' = 1, holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ')'
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
            neg_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ' = 0, Not(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '))'
            result_string += 'Or(' + pos_and + ', ' + neg_and + ')'
        result_string += '))'
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
        result_string = 'A(' + result_string + ' '
        for li in combined_list_of_states:
            combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
            for ca in combined_acts:
                state_act_clause = ''
                implies_precedent = 'A('
                implies_precedent += 'a_' + str(combined_list_of_states.index(li)) + '_' + str(0) + ' = ' + str(ca[0]) + ', a_' + str(
                    combined_list_of_states.index(li)) + '_' + str(1) + ' = ' + str(ca[1]) + ')'
                if 'a_' + str(combined_list_of_states.index(li)) + '_' + str(0) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_' + str(combined_list_of_states.index(li)) + '_' + str(0))
                if 'a_' + str(combined_list_of_states.index(li)) + '_' + str(1) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_' + str(combined_list_of_states.index(li)) + '_' + str(1))
                mul_clause = 'prob_' + str(combined_list_of_states.index(li)) + '_' + str(list_of_subformula.index(formula_duplicate)) + ' = '
                if 'prob_' + str(combined_list_of_states.index(li)) + '_' + str(list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                    list_of_z3_variables.append('prob_' + str(combined_list_of_states.index(li)) + '_' + str(list_of_subformula.index(formula_duplicate)))
                combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])], dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
                implies_antecedent = ''
                first = True
                prod = ''
                for cs in combined_succ:
                    if first:
                        prod = '(' + str(cs[0]) + ' * ' + str(cs[1]) + 'prob_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi1)) + ')'
                        first = False
                    else:
                        prod += '+ (' + str(cs[0]) + ' * ' + str(cs[1]) + 'prob_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi1)) + ')'
                    if 'prob_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi1)) not in list_of_z3_variables:
                        list_of_z3_variables.append('prob_s' + str(combined_succ.index(cs)) + '_' + str(list_of_subformula.index(phi1)))

                mul_clause += prod
                implies_antecedent = '(' + mul_clause + ')'
                state_act_clause = 'Implies(' + implies_precedent + ' ' + implies_antecedent + ')'
                result_string += state_act_clause + ' '
        result_string += ')'

    elif formula_duplicate.data == 'calc_until_unbounded':
        result_string = SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n)
    elif formula_duplicate.data == 'calc_until_bounded':
        result_string = SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)
    elif formula_duplicate.data == 'const':
        c = formula_duplicate.children[0].value
        result_string = 'A('
        first = True
        for li in combined_list_of_states:
            if first:
                result_string += 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + ' = ' + c
                first = False
            else:
                result_string += ', prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)) + ' = ' + c
            if ('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate))) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
        result_string += ')'
    elif formula_duplicate.data in ['add_prob', 'minus_prob', 'mul_prob']:
        left = formula_duplicate.children[0]
        index_left = list_of_subformula.index(left)
        right = formula_duplicate.children[1]
        index_right = list_of_subformula.index(right)
        result_string = 'A(' + Semantics(model, left, combined_list_of_states, n) + ', ' + Semantics(model, right, combined_list_of_states, n) + ')'
        result_string = 'A(' + result_string + ', A('
        op = ''
        for li in combined_list_of_states:
            if formula_duplicate.data == 'add_prob':
                op = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left) + ' + ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right)
            elif formula_duplicate.data == 'minus_prob':
                op = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left) + ' - ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right)
            elif formula_duplicate.data == 'mul_prob':
                op = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left) + ' * ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right)
            result_string += op
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right))
        result_string += '))'

    return result_string


def Truth(model, formula_initial, combined_list_of_states, n):
    list_of_AV = []  # will have the OR,AND according to the quantifier in that index in the formula

    while type(formula_initial.children[0]) == Token:
        if formula_initial.data in ['exist_scheduler', 'forall_scheduler']:
            formula_initial = formula_initial.children[1]
        elif formula_initial.data == 'exist':
            list_of_AV.append('Or')
            formula_initial = formula_initial.children[1]
        elif formula_initial.data == 'forall':
            list_of_AV.append('And')
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
                    result_string += "V(" + "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " ,"
                    if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                        list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
                else:
                    result_string += "A(" + "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " ,"
                    if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                        list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
                first = False
            elif ((i + 1) == len(combined_list_of_states)) or combined_list_of_states[i][0] == combined_list_of_states[i + 1][0] - 1:
                if list_of_AV[1] == 'V':
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + ")"
                    if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                        list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
                else:
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + ")"
                    if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                        list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
            else:
                if list_of_AV[1] == 'V':
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " ,"
                    if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                        list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
                else:
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " ,"
                    if "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) not in list_of_z3_variables:
                        list_of_z3_variables.append("holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi))
        result_string += ')'
    return result_string


def check(F):  # this will take the string F, convert it to z3 compatible equation and return the result of smt checking
    pass


def add_to_subformula_list(formula_phi):  # add as you go any new subformula part as needed
    if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist', 'forall']:
        formula_phi = formula_phi.children[1]
        add_to_subformula_list(formula_phi)
    elif formula_phi.data in ['and_op', 'or_op', 'less_prob', 'greater_prob', 'equal_prob', 'greatereq_prob', 'lesseq_prob', 'add_prob', 'minus_prob', 'mul_prob',
                              'calc_until_unbounded']:
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
        add_to_subformula_list(formula_phi.children[0])


def main_smt_encoding(model, formula_initial, formula):
    F = ""
    sa = ""
    first_i = True
    first_o = True
    list_of_states = []
    F = 'A('

    for state in model.states:
        act = ""
        first_i = True
        sa = 'V('
        for action in state.actions:
            act = "a_" + str(state.id) + " = " + str(action.id)  # a1 means action for state 1
            if "a_" + str(state.id) not in list_of_z3_variables:
                list_of_z3_variables.append("a_" + str(state.id))
            if first_i:
                sa += act
                first_i = False
            else:
                sa += ', ' + act
        sa += ')'
        if first_o:
            F += sa
            first_o = False
        else:
            F += ", " + sa
    F += ')'
    add_to_subformula_list(formula_initial)

    formula_duplicate = formula_initial
    n = 0
    while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist', 'forall']:
            n += 1
            formula_duplicate = formula_duplicate.children[1]
    for state in model.states:
        list_of_states.append(state.id)
    combined_list_of_states = list(itertools.product(list_of_states, repeat=n))

    semantics_result = Semantics(model, formula_duplicate, combined_list_of_states, n)

    if formula_initial.data == 'exist_scheduler':
        truth_result = Truth(model, formula_initial, combined_list_of_states, n)
        F = "A(" + F + "," + semantics_result + "," + truth_result + ")"
        if check(F):
            return True
        else:
            return False
    elif formula_initial.data == 'forall_scheduler':
        new_formula = ''
        i = 0
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
                new_formula += formula[i]
                i += 1
        new_parsed_formula = parser.parse(new_formula)
        truth_result = Truth(model, new_parsed_formula, combined_list_of_states, n)
        F = F + "A (" + semantics_result + ") A (" + truth_result + ")"
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
    result = main_smt_encoding(initial_model, parsed_formula_initial, formula)

# mdp_example_and "ES sh . E s1 . E s2 . ( one(s1) & two(s2) )" s1 and s2 are dtmcs extended by using scheduler sh on the mdp example_and.nm
# mdp_example_neg_const "ES sh . E s1 . E s2 . (P(X ( one(s1) & two(s2) ) > 3)"
# mdp_example_neg_const "ES sh . E s1 . E s2 . ~one(s1)"
# mdp_example_neg_const "ES sh . E s1 . E s2 . (P(X ( one(s1) ) > 3)"
