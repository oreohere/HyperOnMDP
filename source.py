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
    z = Bool('z')
    z1 = Bool('z1')
    s = Solver()
    s.add(And(Or(x1 == 1, x1 == 3), z == True, z1 == False, And(z, z1)))
    s.add(y == 2)
    s.add(x1 + y == 5)
    t = s.check()
    print("Hi")


def Semantics(model, formula_duplicate, n):
    E = ""
    return E


def Truth(model, formula_initial, n):
    list_of_states = []
    list_of_AV = []  # will have the or, and according to the quantifier in that index in the formula
    for state in model.states:
        list_of_states.append(state.id)
    combined_list_of_states = list(itertools.product(list_of_states, repeat=n))
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
            if first or combined_list_of_states[i-1][0] == combined_list_of_states[i][0] - 1:
                if list_of_AV[1] == 'V':
                    result_string += "V(" + "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " ,"
                else:
                    result_string += "A(" + "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " ,"
                first = False
            elif ((i+1) == len(combined_list_of_states)) or combined_list_of_states[i][0] == combined_list_of_states[i+1][0] - 1:
                if list_of_AV[1] == 'V':
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + ")"
                else:
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + ")"
            else:
                if list_of_AV[1] == 'V':
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " ,"
                else:
                    result_string += "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(index_of_phi) + " ,"
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
    elif formula_phi.data in ['var', 'true', 'const', 'calc_next']:
        list_of_subformula.append(formula_phi)
    elif formula_phi.data in ['neg_op']:
        list_of_subformula.append(formula_phi)
        formula_phi = formula_phi.children[1]
        list_of_subformula.append(formula_phi)


def main_smt_encoding(model, formula_initial, formula):
    F = ""
    sa = ""
    first_i = True
    first_o = True
    F = 'A('
    for state in model.states:
        act = ""
        first_i = True
        sa = 'V('
        for action in state.actions:
            act = "a" + str(state.id) + " = " + str(action.id)   # a1 means action for state 1
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
    while type(formula_duplicate.children[0]) == Token:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist', 'forall']:
            n += 1
            formula_duplicate = formula_duplicate.children[1]

    semantics_result = Semantics(model, formula_duplicate, n)

    if formula_initial.data == 'exist_scheduler':
        truth_result = Truth(model, formula_initial, n)
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
        truth_result = Truth(model, new_parsed_formula, n)
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
