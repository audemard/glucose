/************************************=== CCAnr ===***************************************
 ** CCAnr is a local search solver for the Boolean Satisfiability (SAT) problem,
 ** which is especially designed for non-random instances.
 ** CCAnr is designed and implemented by Shaowei Cai (email: shaoweicai.cs@gmail.com),
 *****************************************************************************************/

/*****************************=== Develpment history ===*************************************
** 2011.5
** SWCC (Smoothed Weighting and Configuration Checking) by Shaowei Cai
** New Idea: Configuration Checking (CC)
** A variable is configuration changed, if since its last flip, at least one of its
** neighboring var has been flipped.
** In the greedy mode, Swcc picks the best Configuration Changed Decreasing  var to flip.
** In the random mode, it updates weights, and flips the oldest var in a random unsat clause.

** 2011.9
** SWCCA (Smoothed Weighting and Configuration Checking with Aspiration) by Shaowei Cai
** New Idea: CC with Aspiration (CCA)
** Modification: in greedy mode, it first prefers to flip the best CCD var. If there is
** no CCD variable, then flip the best significant decreasing var, i.e., with a great
** positive score (in Swcca, bigger than averaged clause weight), if there exsit such vars.

** 2013.4
** CCAnr (CCA for non-random SAT)
** Modifications: Generalize the smoothig fomula as w(ci)=w(ci)*p+ave_w*q; pick the greediest
** variable in the diversification mode.
************************************************************************************************/


#ifndef GLUCOSE_CCANR_H
#define GLUCOSE_CCANR_H
#include <utils/Random.h>

#include "SolverTypes.h"

#define _pop(stack)           stack[--stack##_fill_pointer]
#define _push(item, stack)    stack[stack##_fill_pointer++] = item
#define litGlucose2CCANR(lit) ((sign(lit) ? -1 : 1) * (var(lit) + 1))

namespace Glucose {

struct lit {
    unsigned char sense : 1;         // is 1 for true literals, 0 for false literals.
    int           clause_num : 31;   // clause num, begin with 0
    int           var_num;           // variable num, begin with 1
};

struct variable {
    int      score;
    int      time_stamp;
    int      conf_change;
    vec<int> var_neighbor;
};

struct clause {
    int weight;
    int sat_count;
    int sat_var;
};

class Solver;
class CCANR {
    Solver& solver;

    // parameters of the instance
    int           num_vars;      // var index from 1 to num_vars
    int           num_clauses;   // clause index from 0 to num_clauses-1
    bool          aspiration_active = true;
    unsigned long mems              = 0;
    unsigned long memsLimit         = 25 * 1000 * 1000;


    /* literal arrays */


    vec<lit*>     var_lit;            // var_lit[i][j] means the j'th literal of var i.
    vec<int>      var_lit_count;      // amount of literals of each var
    vec<lit*>     clause_lit;         // clause_lit[i][j] means the j'th literal of clause i.
    vec<int>      clause_lit_count;   // amount of literals in each clause
    vec<variable> variables;
    vec<clause>   clauses;

    Random& random;

    // unsat clauses stack
    vec<int> unsat_stack;   // store the unsat clause number
    int      unsat_stack_fill_pointer;
    vec<int> index_in_unsat_stack;   // which position is a clause in the unsat_stack

    int this_try_best_unsat_stack_fill_pointer;
    int n_unsat_clausesbest;
    // variables in unsat clauses
    vec<int> unsatvar_stack;
    int      unsatvar_stack_fill_pointer;
    vec<int> index_in_unsatvar_stack;
    vec<int> unsat_app_count;   // a varible appears in how many unsat clauses

    // configuration changed decreasing variables (score>0 and confchange=1)
    vec<int> goodvar_stack;
    int      goodvar_stack_fill_pointer;
    vec<int> already_in_goodvar_stack;


    /* Information about solution */
    vec<int> cur_soln;   // the current solution, with 1's for True variables, and 0's for False variables

    // cutoff
    int       max_tries          = 100;
    long long ls_no_improv_times = 200000;

    int tries;
    int step;

    int ave_weight         = 1;
    int delta_total_weight = 0;

    /**************************************** clause weighting for 3sat **************************************************/

    int   threshold = 50;
    float p_scale   = 0.3;   // w=w*p+ave_w*q
    float q_scale   = 0.7;
    int   scale_ave;   // scale_ave==ave_weight*q_scale


   public:
    explicit CCANR(Solver& _solver);
    void addClauses(vec<CRef>& clauses);
    int  build_instance();
    void createSpace(int nbclauses);
    void build_neighbor_relation();

    void init(int t);

    lbool solve();
    void  local_search(long long no_improv_times);
    int   pick_var();
    void  flip(int flipvar);

    void update_clause_weights();
    void smooth_clause_weights();

    void bumpVSIDSScores();

    bool assignedToTrue(Var v) { return cur_soln[v + 1] == 1; }


    inline void unsat(int clause) {
        index_in_unsat_stack[clause] = unsat_stack_fill_pointer;
        _push(clause, unsat_stack);

        // update appreance count of each var in unsat clause and update stack of vars in unsat clauses
        int v;
        for(lit* p = clause_lit[clause]; (v = p->var_num) != 0; p++) {
            unsat_app_count[v]++;
            if(unsat_app_count[v] == 1) {
                index_in_unsatvar_stack[v] = unsatvar_stack_fill_pointer;
                _push(v, unsatvar_stack);
            }
        }
    }


    inline void sat(int clause) {
        int index, last_unsat_clause;

        // since the clause is satisfied, its position can be reused to store the last_unsat_clause
        last_unsat_clause                       = _pop(unsat_stack);
        index                                   = index_in_unsat_stack[clause];
        unsat_stack[index]                      = last_unsat_clause;
        index_in_unsat_stack[last_unsat_clause] = index;

        // update appreance count of each var in unsat clause and update stack of vars in unsat clauses
        int v, last_unsat_var;
        for(lit* p = clause_lit[clause]; (v = p->var_num) != 0; p++) {
            unsat_app_count[v]--;
            if(unsat_app_count[v] == 0) {
                last_unsat_var                          = _pop(unsatvar_stack);
                index                                   = index_in_unsatvar_stack[v];
                unsatvar_stack[index]                   = last_unsat_var;
                index_in_unsatvar_stack[last_unsat_var] = index;
            }
        }
    }
};

}   // namespace Glucose


#endif   // GLUCOSE_CCANR_H
