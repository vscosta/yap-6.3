#include <cassert>

#include "BayesBall.h"


namespace horus {

BayesBall::BayesBall (FactorGraph& fg)
    : fg_(fg) , dag_(fg.getStructure())
{
  dag_.clear();
}



FactorGraph*
BayesBall::getMinimalFactorGraph (FactorGraph& fg, VarIds vids)
{
  BayesBall bb (fg);
  return bb.getMinimalFactorGraph (vids);
}



FactorGraph*
BayesBall::getMinimalFactorGraph (const VarIds& queryIds)
{
  assert (fg_.bayesianFactors());
  Scheduling scheduling;
  for (size_t i = 0; i < queryIds.size(); i++) {
    assert (dag_.getNode (queryIds[i]));
    BBNode* n = dag_.getNode (queryIds[i]);
    scheduling.push (ScheduleInfo (n, false, true));
  }

  while (!scheduling.empty()) {
    ScheduleInfo& sch = scheduling.front();
    BBNode* n = sch.node;
    n->setAsVisited();
    if (n->hasEvidence() == false && sch.visitedFromChild) {
      if (n->isMarkedOnTop() == false) {
        n->markOnTop();
        scheduleParents (n, scheduling);
      }
      if (n->isMarkedOnBottom() == false) {
        n->markOnBottom();
        scheduleChilds (n, scheduling);
      }
    }
    if (sch.visitedFromParent) {
      if (n->hasEvidence() && n->isMarkedOnTop() == false) {
        n->markOnTop();
        scheduleParents (n, scheduling);
      }
      if (n->hasEvidence() == false && n->isMarkedOnBottom() == false) {
        n->markOnBottom();
        scheduleChilds (n, scheduling);
      }
    }
    scheduling.pop();
  }

  FactorGraph* fg = new FactorGraph();
  constructGraph (fg);
  return fg;
}



void
BayesBall::constructGraph (FactorGraph* fg) const
{
  const FacNodes& facNodes = fg_.facNodes();
  for (size_t i = 0; i < facNodes.size(); i++) {
    const BBNode* n = dag_.getNode (
        facNodes[i]->factor().argument (0));
    if (n->isMarkedOnTop()) {
      fg->addFactor (facNodes[i]->factor());
    } else if (n->hasEvidence() && n->isVisited()) {
      VarIds varIds = { facNodes[i]->factor().argument (0) };
      Ranges ranges = { facNodes[i]->factor().range (0) };
      Params params (ranges[0], log_aware::noEvidence());
      params[n->getEvidence()] = log_aware::withEvidence();
      fg->addFactor (Factor (varIds, ranges, params));
    }
  }
  const VarNodes& varNodes = fg_.varNodes();
  for (size_t i = 0; i < varNodes.size(); i++) {
    if (varNodes[i]->hasEvidence()) {
      VarNode* vn = fg->getVarNode (varNodes[i]->varId());
      if (vn) {
        vn->setEvidence (varNodes[i]->getEvidence());
      }
    }
  }
}

}  // namespace horus

