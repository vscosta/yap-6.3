#include <cassert>

#include <vector>
#include <string>
#include <iostream>

#include "GroundSolver.h"
#include "VarElim.h"
#include "BeliefProp.h"
#include "CountingBp.h"
#include "Util.h"


namespace horus {

void
GroundSolver::printAnswer (const VarIds& vids)
{
  Vars   unobservedVars;
  VarIds unobservedVids;
  for (size_t i = 0; i < vids.size(); i++) {
    VarNode* vn = fg.getVarNode (vids[i]);
    if (vn->hasEvidence() == false) {
      unobservedVars.push_back (vn);
      unobservedVids.push_back (vids[i]);
    }
  }
  if (unobservedVids.empty() == false) {
    Params res = solveQuery (unobservedVids);
    std::vector<std::string> stateLines =
        util::getStateLines (unobservedVars);
    for (size_t i = 0; i < res.size(); i++) {
      std::cout << "P(" << stateLines[i] << ") = " ;
      std::cout << std::setprecision (constants::PRECISION) << res[i];
      std::cout << std::endl;
    }
    std::cout << std::endl;
  }
}



void
GroundSolver::printAllPosterioris (void)
{
  VarNodes vars = fg.varNodes();
  std::sort (vars.begin(), vars.end(), sortByVarId());
  for (size_t i = 0; i < vars.size(); i++) {
    printAnswer ({vars[i]->varId()});
  }
}



Params
GroundSolver::getJointByConditioning (
    GroundSolverType solverType,
    FactorGraph fg,
    const VarIds& jointVarIds)
{
  VarNodes jointVars;
  for (size_t i = 0; i < jointVarIds.size(); i++) {
    assert (fg.getVarNode (jointVarIds[i]));
    jointVars.push_back (fg.getVarNode (jointVarIds[i]));
  }

  GroundSolver* solver = 0;
  switch (solverType) {
    case GroundSolverType::BP:  solver = new BeliefProp (fg); break;
    case GroundSolverType::CBP: solver = new CountingBp (fg); break;
    case GroundSolverType::VE:  solver = new VarElim (fg);    break;
  }
  Params prevBeliefs = solver->solveQuery ({jointVarIds[0]});
  VarIds observedVids = {jointVars[0]->varId()};

  for (size_t i = 1; i < jointVarIds.size(); i++) {
    assert (jointVars[i]->hasEvidence() == false);
    Params newBeliefs;
    Vars observedVars;
    Ranges observedRanges;
    for (size_t j = 0; j < observedVids.size(); j++) {
      observedVars.push_back (fg.getVarNode (observedVids[j]));
      observedRanges.push_back (observedVars.back()->range());
    }
    Indexer indexer (observedRanges, false);
    while (indexer.valid()) {
      for (size_t j = 0; j < observedVars.size(); j++) {
        observedVars[j]->setEvidence (indexer[j]);
      }
      delete solver;
      switch (solverType) {
        case GroundSolverType::BP:  solver = new BeliefProp (fg); break;
        case GroundSolverType::CBP: solver = new CountingBp (fg); break;
        case GroundSolverType::VE:  solver = new VarElim (fg);    break;
      }
      Params beliefs = solver->solveQuery ({jointVarIds[i]});
      for (size_t k = 0; k < beliefs.size(); k++) {
        newBeliefs.push_back (beliefs[k]);
      }
      ++ indexer;
    }

    int count = -1;
    for (size_t j = 0; j < newBeliefs.size(); j++) {
      if (j % jointVars[i]->range() == 0) {
        count ++;
      }
      newBeliefs[j] *= prevBeliefs[count];
    }
    prevBeliefs = newBeliefs;
    observedVids.push_back (jointVars[i]->varId());
  }
  delete solver;
  return prevBeliefs;
}

}  // namespace horus

