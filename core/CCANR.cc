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


#include "core/CCANR.h"

#include <cstdlib>
#include <iostream>

#include "core/Solver.h"
#include "utils/System.h"
using namespace Glucose;
using namespace std;

CCANR::CCANR(Solver& _solver) : solver(_solver), random(_solver.random) { }

void CCANR::bumpVSIDSScores() {
    vec<int> nbBumped;
    // solver.varDecayActivity();
    // solver.varDecayActivity();

    vec<int> seenClauses;
    vec<int> seenVars;
    seenVars.growTo(num_vars + 1, 0);
    seenClauses.growTo(num_clauses + 1, 0);
    int clauseToBump;
    int nb = 0;
    while(true) {
        int best = -1;
        if(nb >= 100 || nb > num_vars) return;
        clauseToBump = -1;
        for(int c = 0; c < num_clauses; c++) {
            if(seenClauses[c] == 1) continue;
            if(clauses[c].weight > best) {
                best         = clauses[c].weight;
                clauseToBump = c;
            }
        }
        if(clauseToBump == -1 || best == -1) return;
        for(int k = 0; k < clause_lit_count[clauseToBump]; ++k) {
            int v = clause_lit[clauseToBump][k].var_num;
            if(seenVars[v] >= 100) continue;
            solver.varBumpActivity(v - 1);
            seenVars[v]++;
            nb++;
        }
        seenClauses[clauseToBump] = 1;
    }
}


int CCANR::pick_var() {
    int  i, k, c, v;
    int  best_var;
    lit* clause_c;

    mems += num_vars / 8;


    /**Greedy Mode**/
    /*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
    if(goodvar_stack_fill_pointer > 0) {
        best_var = goodvar_stack[0];
        for(i = 1; i < goodvar_stack_fill_pointer; ++i) {
            variable& var  = variables[goodvar_stack[i]];
            variable& best = variables[best_var];
            if(var.score > best.score)
                best_var = goodvar_stack[i];
            else if(var.score == best.score) {
                if(var.time_stamp < best.time_stamp) best_var = goodvar_stack[i];
            }
        }
        return best_var;
    }


    /*aspiration*/
    if(aspiration_active) {
        best_var = 0;
        for(i = 0; i < unsatvar_stack_fill_pointer; ++i) {
            if(variables[unsatvar_stack[i]].score > ave_weight) {
                best_var = unsatvar_stack[i];
                break;
            }
        }

        for(++i; i < unsatvar_stack_fill_pointer; ++i) {
            variable& var  = variables[unsatvar_stack[i]];
            variable& best = variables[best_var];
            if(var.score > best.score || (var.score == best.score && var.time_stamp < best.time_stamp))
                best_var = unsatvar_stack[i];
        }

        if(best_var != 0) return best_var;
    }
    /*****end aspiration*******************/

    update_clause_weights();

    /*focused random walk*/

    c        = unsat_stack[random.nextInt(unsat_stack_fill_pointer)];
    clause_c = clause_lit[c];
    best_var = clause_c[0].var_num;
    for(k = 1; k < clause_lit_count[c]; ++k) {
        v              = clause_c[k].var_num;
        variable& var  = variables[v];
        variable& best = variables[best_var];
        // using unweighted make
        if(unsat_app_count[v] > unsat_app_count[best_var])
            best_var = v;

        else if(unsat_app_count[v] == unsat_app_count[best_var]) {
            if(var.score > best.score || (var.score == best.score && var.time_stamp < best.time_stamp)) best_var = v;
        }
    }
    return best_var;
}


void CCANR::addClauses(vec<CRef>& _clauses) {
    // Now, read the clauses, one at a time.
    vec<int> temp_lit;

    temp_lit.growTo(num_vars + 1);

    for(CRef cr : _clauses) {
        temp_lit.clear();
        Clause& clause = solver.ca[cr];

        for(int i = 0; i < clause.size(); i++) {
            if(solver.value(clause[i]) != l_Undef && solver.level(var(clause[i])) == 0) {
                if(solver.value(clause[i]) == l_False)   // UNSAT Lit
                    continue;
                // SAT Clause
                goto splitclause;
            }
            temp_lit.push(litGlucose2CCANR(clause[i]));
        }
        clause_lit[num_clauses] = new lit[temp_lit.size() + 1];
        int i;
        clause_lit_count[num_clauses] = temp_lit.size();
        for(i = 0; i < temp_lit.size(); ++i) {
            clause_lit[num_clauses][i].clause_num = num_clauses;
            clause_lit[num_clauses][i].var_num    = abs(temp_lit[i]);
            clause_lit[num_clauses][i].sense      = temp_lit[i] > 0 ? 1 : 0;

            var_lit_count[clause_lit[num_clauses][i].var_num]++;
        }
        clause_lit[num_clauses][i].var_num    = 0;
        clause_lit[num_clauses][i].clause_num = -1;
        num_clauses++;

    splitclause:;
    }
}


/*
 * Read in the problem.
 */
int CCANR::build_instance() {
    int i;
    int v, c;   // var, clause


    /*** build problem data structures of the instance ***/
    num_vars    = solver.nVars();
    num_clauses = 0;

    vec<CRef> coresClauses;
    for(CRef cr : solver.learntsCore)
        if(solver.ca[cr].lbd() <= 3) coresClauses.push(cr);

    createSpace(solver.clauses.size() + coresClauses.size());


    for(c = 0; c < solver.clauses.size() + coresClauses.size(); c++) clause_lit_count[c] = 0;
    for(v = 1; v <= num_vars; ++v) var_lit_count[v] = 0;

    addClauses(solver.clauses);
    // addClauses(coresClauses);

    // creat var literal arrays
    for(v = 1; v <= num_vars; ++v) {
        var_lit[v]       = new lit[var_lit_count[v] + 1];
        var_lit_count[v] = 0;   // reset to 0, for build up the array
    }
    // scan all clauses to build up var literal arrays
    for(c = 0; c < num_clauses; ++c) {
        for(i = 0; i < clause_lit_count[c]; ++i) {
            v                            = clause_lit[c][i].var_num;
            var_lit[v][var_lit_count[v]] = clause_lit[c][i];
            ++var_lit_count[v];
        }
    }
    for(v = 1; v <= num_vars; ++v)   // set boundary
        var_lit[v][var_lit_count[v]].clause_num = -1;

    return 1;
}


void CCANR::build_neighbor_relation() {
    int* neighbor_flag = new int[num_vars + 1];
    int  i, j, count = 0;
    int  v, c;

    for(v = 1; v <= num_vars; ++v) {
        variables[v].var_neighbor.clear();

        for(i = 1; i <= num_vars; ++i) neighbor_flag[i] = 0;
        neighbor_flag[v] = 1;

        for(i = 0; i < var_lit_count[v]; ++i) {
            c = var_lit[v][i].clause_num;

            for(j = 0; j < clause_lit_count[c]; ++j) {
                if(neighbor_flag[clause_lit[c][j].var_num] == 0) {
                    count++;
                    neighbor_flag[clause_lit[c][j].var_num] = 1;
                }
            }
        }

        neighbor_flag[v] = 0;

        for(i = 1; i <= num_vars; ++i)
            if(neighbor_flag[i] == 1) variables[v].var_neighbor.push(i);
    }

    delete[] neighbor_flag;
}

void CCANR::local_search(long long no_improv_times) {
    int       flipvar;
    long long notime = 1 + no_improv_times;

    while(--notime) {
        step++;

        flipvar = pick_var();
        flip(flipvar);
        solver.stats[Stats::nbFlips]++;
        variables[flipvar].time_stamp = step;

        if(unsat_stack_fill_pointer < this_try_best_unsat_stack_fill_pointer) {
            this_try_best_unsat_stack_fill_pointer = unsat_stack_fill_pointer;
            notime                                 = 1 + no_improv_times;
        }


        if(n_unsat_clausesbest > unsat_stack_fill_pointer) {
            n_unsat_clausesbest = unsat_stack_fill_pointer;
            for(int i = 1; i <= num_vars; i++) solver.targetPolarity[i - 1] = (cur_soln[i] == 0);
        }

        if(unsat_stack_fill_pointer == 0) return;
    }
}


lbool CCANR::solve() {
    double initialTime = cpuTime();
    build_instance();
    // sscanf(argv[2],"%d",&seed);
    solver.stats[Stats::nbWalk]++;
    mems                = 0;
    n_unsat_clausesbest = num_clauses;

    build_neighbor_relation();

    scale_ave = (threshold + 1) * q_scale;   //


    for(tries = 0; tries <= max_tries; tries++) {
        init(tries);

        local_search(ls_no_improv_times);

        if(unsat_stack_fill_pointer == 0) {
            solver.solvedByLS = true;
            break;
        }
        if(mems > memsLimit) break;
    }
    solver.stats[Stats::walkTime] += ((int)(cpuTime() - initialTime));
    // TODO -> free memory
    // free_memory();
    if(unsat_stack_fill_pointer == 0) return l_True;

    bumpVSIDSScores();

    return l_Undef;
}

void CCANR::init(int t) {
    int v, c;
    int i, j;

    // Initialize edge weights
    for(c = 0; c < num_clauses; c++) clauses[c].weight = 1;

    // init unsat_stack
    unsat_stack_fill_pointer    = 0;
    unsatvar_stack_fill_pointer = 0;

    // init solution
    if(t == 0)
        for(v = 1; v <= num_vars; v++)
            cur_soln[v] = solver.targetPolarity[v - 1] == -10 ? random.nextDouble() < 2 : !solver.targetPolarity[v - 1];
    else
        for(v = 1; v <= num_vars; v++) cur_soln[v] = random.nextDouble() < 2;


    for(v = 1; v <= num_vars; v++) {
        variables[v].time_stamp  = 0;
        variables[v].conf_change = 1;
        unsat_app_count[v]       = 0;
    }

    /* figure out sat_count, and init unsat_stack */
    for(c = 0; c < num_clauses; ++c) {
        clauses[c].sat_count = 0;

        for(j = 0; j < clause_lit_count[c]; ++j) {
            if(cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {
                clauses[c].sat_count++;
                clauses[c].sat_var = clause_lit[c][j].var_num;
            }
        }

        if(clauses[c].sat_count == 0) unsat(c);
    }

    /*figure out var score*/
    int lit_count;
    for(v = 1; v <= num_vars; v++) {
        variables[v].score = 0;

        lit_count = var_lit_count[v];

        for(i = 0; i < lit_count; ++i) {
            c = var_lit[v][i].clause_num;
            if(clauses[c].sat_count == 0)
                variables[v].score++;
            else if(clauses[c].sat_count == 1 && var_lit[v][i].sense == cur_soln[v])
                variables[v].score--;
        }
    }


    // init goodvars stack
    goodvar_stack_fill_pointer = 0;
    for(v = 1; v <= num_vars; v++) {
        if(variables[v].score > 0) {
            already_in_goodvar_stack[v] = 1;
            _push(v, goodvar_stack);
        } else
            already_in_goodvar_stack[v] = 0;
    }

    // setting for the virtual var 0
    variables[0].time_stamp = 0;
    // pscore[0]=0;

    this_try_best_unsat_stack_fill_pointer = unsat_stack_fill_pointer;
}


void CCANR::flip(int flipvar) {
    cur_soln[flipvar] = 1 - cur_soln[flipvar];

    int v, c;

    lit* clause_c;

    int org_flipvar_score = variables[flipvar].score;

    // update related clauses and neighbor vars
    for(lit* q = var_lit[flipvar]; (c = q->clause_num) >= 0; q++) {
        mems++;
        clause_c = clause_lit[c];
        if(cur_soln[flipvar] == q->sense) {
            clauses[c].sat_count++;

            if(clauses[c].sat_count == 2)   // sat_count from 1 to 2
                variables[clauses[c].sat_var].score += clauses[c].weight;
            else if(clauses[c].sat_count == 1)   // sat_count from 0 to 1
            {
                clauses[c].sat_var = flipvar;   // record the only true lit's var
                for(lit* p = clause_c; (v = p->var_num) != 0; p++) variables[v].score -= clauses[c].weight;

                sat(c);
            }
        } else {
            clauses[c].sat_count--;
            if(clauses[c].sat_count == 1) {   // sat_count from 2 to 1
                for(lit* p = clause_c; (v = p->var_num) != 0; p++) {
                    if(p->sense == cur_soln[v]) {
                        variables[v].score -= clauses[c].weight;
                        clauses[c].sat_var = v;
                        break;
                    }
                }
            } else if(clauses[c].sat_count == 0) {   // sat_count from 1 to 0
                for(lit* p = clause_c; (v = p->var_num) != 0; p++) variables[v].score += clauses[c].weight;
                unsat(c);
            }   // end else if

        }   // end else
    }

    variables[flipvar].score = -org_flipvar_score;

    /*update CCD */
    int index;

    variables[flipvar].conf_change = 0;

    // remove the vars no longer goodvar in goodvar stack
    mems += goodvar_stack_fill_pointer / 4;

    for(index = goodvar_stack_fill_pointer - 1; index >= 0; index--) {
        v = goodvar_stack[index];
        if(variables[v].score <= 0) {
            goodvar_stack[index]        = _pop(goodvar_stack);
            already_in_goodvar_stack[v] = 0;
        }
    }

    // update all flipvar's neighbor's conf_change to be 1, add goodvar
    unsigned long tmp = 0;
    for(int v2 : variables[flipvar].var_neighbor) {
        tmp++;
        variables[v2].conf_change = 1;

        if(variables[v2].score > 0 && already_in_goodvar_stack[v2] == 0) {
            _push(v2, goodvar_stack);
            already_in_goodvar_stack[v2] = 1;
        }
    }
    mems += tmp / 4;
}


void CCANR::update_clause_weights() {
    int i, v;

    for(i = 0; i < unsat_stack_fill_pointer; ++i) clauses[unsat_stack[i]].weight++;

    for(i = 0; i < unsatvar_stack_fill_pointer; ++i) {
        v = unsatvar_stack[i];
        variables[v].score += unsat_app_count[v];
        if(variables[v].score > 0 && variables[v].conf_change == 1 && already_in_goodvar_stack[v] == 0) {
            _push(v, goodvar_stack);
            already_in_goodvar_stack[v] = 1;
        }
    }

    delta_total_weight += unsat_stack_fill_pointer;
    if(delta_total_weight >= num_clauses) {
        ave_weight += 1;
        delta_total_weight -= num_clauses;

        // smooth weights
        if(ave_weight > threshold) smooth_clause_weights();
    }
}


void CCANR::smooth_clause_weights() {
    int j, c, v;
    int new_total_weight = 0;

    for(v = 1; v <= num_vars; ++v) variables[v].score = 0;

    // smooth clause score and update score of variables
    mems += num_clauses;
    for(c = 0; c < num_clauses; ++c) {
        clauses[c].weight = clauses[c].weight * p_scale + scale_ave;
        if(clauses[c].weight < 1) clauses[c].weight = 1;

        new_total_weight += clauses[c].weight;

        // update score of variables in this clause
        if(clauses[c].sat_count == 0)
            for(j = 0; j < clause_lit_count[c]; ++j) variables[clause_lit[c][j].var_num].score += clauses[c].weight;
        else if(clauses[c].sat_count == 1)
            variables[clauses[c].sat_var].score -= clauses[c].weight;
    }

    ave_weight = new_total_weight / num_clauses;
}

void CCANR::createSpace(int nbclauses) {
    // Create space
    int sz = nbclauses;
    var_lit.growTo(num_vars + 1);
    var_lit_count.growTo(num_vars + 1);
    clause_lit.growTo(sz);
    clause_lit_count.growTo(sz);

    variables.growTo(num_vars + 1);
    clauses.growTo(sz);

    unsat_stack.growTo(sz);
    index_in_unsat_stack.growTo(sz);

    unsatvar_stack.growTo(num_vars + 1);
    index_in_unsatvar_stack.growTo(num_vars + 1);
    unsat_app_count.growTo(num_vars + 1);

    goodvar_stack.growTo(num_vars + 1);
    already_in_goodvar_stack.growTo(num_vars + 1);
    cur_soln.growTo(num_vars + 1);
}