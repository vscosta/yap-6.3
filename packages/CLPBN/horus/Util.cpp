#include "Util.h"
#include "Indexer.h"
#include "ElimGraph.h"
#include "BeliefProp.h"


namespace horus {

namespace globals {

bool logDomain = false;

unsigned verbosity = 0;

LiftedSolverType liftedSolver = LiftedSolverType::LVE;

GroundSolverType groundSolver = GroundSolverType::VE;

}



namespace util {

template <> std::string
toString (const bool& b)
{
  std::stringstream ss;
  ss << std::boolalpha << b;
  return ss.str();
}



unsigned
stringToUnsigned (std::string str)
{
  int val;
  std::stringstream ss;
  ss << str;
  ss >> val;
  if (val < 0) {
    std::cerr << "Error: the number readed is negative." << std::endl;
    exit (EXIT_FAILURE);
  }
  return static_cast<unsigned> (val);
}



double
stringToDouble (std::string str)
{
  double val;
  std::stringstream ss;
  ss << str;
  ss >> val;
  return val;
}



double
factorial (unsigned num)
{
  double result = 1.0;
  for (unsigned i = 1; i <= num; i++) {
    result *= i;
  }
  return result;
}



double
logFactorial (unsigned num)
{
  double result = 0.0;
  if (num < 150) {
    result = std::log (factorial (num));
  } else {
    for (unsigned i = 1; i <= num; i++) {
      result += std::log (i);
    }
  }
  return result;
}



unsigned
nrCombinations (unsigned n, unsigned k)
{
  assert (n >= k);
  int diff = n - k;
  unsigned result = 0;
  if (n < 150) {
    unsigned prod = 1;
    for (int i = n; i > diff; i--) {
      prod *= i;
    }
    result = prod / factorial (k);
  } else {
    double prod = 0.0;
    for (int i = n; i > diff; i--) {
      prod += std::log (i);
    }
    prod -= logFactorial (k);
    result = static_cast<unsigned> (std::exp (prod));
  }
  return result;
}



size_t
sizeExpected (const Ranges& ranges)
{
  return std::accumulate (ranges.begin(),
      ranges.end(), 1, std::multiplies<unsigned>());
}



unsigned
nrDigits (int num)
{
  unsigned count = 1;
  while (num >= 10) {
    num /= 10;
    count ++;
  }
  return count;
}



bool
isInteger (const std::string& s)
{
  std::stringstream ss1 (s);
  std::stringstream ss2;
  int integer;
  ss1 >> integer;
  ss2 << integer;
  return (ss1.str() == ss2.str());
}



std::string
parametersToString (const Params& v, unsigned precision)
{
  std::stringstream ss;
  ss.precision (precision);
  ss << "[" ;
  for (size_t i = 0; i < v.size(); i++) {
    if (i != 0) ss << ", " ;
    ss << v[i];
  }
  ss << "]" ;
  return ss.str();
}



std::vector<std::string>
getStateLines (const Vars& vars)
{
  Ranges ranges;
  for (size_t i = 0; i < vars.size(); i++) {
    ranges.push_back (vars[i]->range());
  }
  Indexer indexer (ranges);
  std::vector<std::string> jointStrings;
  while (indexer.valid()) {
    std::stringstream ss;
    for (size_t i = 0; i < vars.size(); i++) {
      if (i != 0) ss << ", " ;
      ss << vars[i]->label() << "=" ;
      ss << vars[i]->states()[(indexer[i])];
    }
    jointStrings.push_back (ss.str());
    ++ indexer;
  }
  return jointStrings;
}



bool invalidValue (std::string option, std::string value)
{
  std::cerr << "Warning: invalid value `" << value << "' " ;
  std::cerr << "for `" << option << "'." ;
  std::cerr << std::endl;
  return false;
}



bool
setHorusFlag (std::string option, std::string value)
{
  bool returnVal = true;
  if (option == "lifted_solver") {
    if      (value == "lve")  globals::liftedSolver = LiftedSolverType::LVE;
    else if (value == "lbp")  globals::liftedSolver = LiftedSolverType::LBP;
    else if (value == "lkc")  globals::liftedSolver = LiftedSolverType::LKC;
    else                      returnVal = invalidValue (option, value);

  } else if (option == "ground_solver" || option == "solver") {
    if      (value == "hve")  globals::groundSolver = GroundSolverType::VE;
    else if (value == "bp")   globals::groundSolver = GroundSolverType::BP;
    else if (value == "cbp")  globals::groundSolver = GroundSolverType::CBP;
    else                      returnVal = invalidValue (option, value);

  } else if (option == "verbosity") {
    std::stringstream ss;
    ss << value;
    ss >> globals::verbosity;

  } else if (option == "use_logarithms") {
    if      (value == "true")  globals::logDomain = true;
    else if (value == "false") globals::logDomain = false;
    else                       returnVal = invalidValue (option, value);

  } else if (option == "hve_elim_heuristic") {
    if      (value == "sequential")
      ElimGraph::setElimHeuristic (ElimHeuristic::SEQUENTIAL);
    else if (value == "min_neighbors")
      ElimGraph::setElimHeuristic (ElimHeuristic::MIN_NEIGHBORS);
    else if (value == "min_weight")
      ElimGraph::setElimHeuristic (ElimHeuristic::MIN_WEIGHT);
    else if (value == "min_fill")
      ElimGraph::setElimHeuristic (ElimHeuristic::MIN_FILL);
    else if (value == "weighted_min_fill")
      ElimGraph::setElimHeuristic (ElimHeuristic::WEIGHTED_MIN_FILL);
    else
      returnVal = invalidValue (option, value);

  } else if (option == "bp_msg_schedule") {
    if      (value == "seq_fixed")
      BeliefProp::setMsgSchedule (MsgSchedule::SEQ_FIXED);
    else if (value == "seq_random")
      BeliefProp::setMsgSchedule (MsgSchedule::SEQ_RANDOM);
    else if (value == "parallel")
      BeliefProp::setMsgSchedule (MsgSchedule::PARALLEL);
    else if (value == "max_residual")
      BeliefProp::setMsgSchedule (MsgSchedule::MAX_RESIDUAL);
    else
      returnVal = invalidValue (option, value);

  } else if (option == "bp_accuracy") {
    std::stringstream ss;
    double acc;
    ss << value;
    ss >> acc;
    BeliefProp::setAccuracy (acc);

  } else if (option == "bp_max_iter") {
    std::stringstream ss;
    unsigned mi;
    ss << value;
    ss >> mi;
    BeliefProp::setMaxIterations (mi);

  } else if (option == "export_libdai") {
    if      (value == "true")  FactorGraph::enableExportToLibDai();
    else if (value == "false") FactorGraph::disableExportToLibDai();
    else                       returnVal = invalidValue (option, value);

  } else if (option == "export_uai") {
    if      (value == "true")  FactorGraph::enableExportToUai();
    else if (value == "false") FactorGraph::disableExportToUai();
    else                       returnVal = invalidValue (option, value);

  } else if (option == "export_graphviz") {
    if      (value == "true")  FactorGraph::enableExportToGraphViz();
    else if (value == "false") FactorGraph::disableExportToGraphViz();
    else                       returnVal = invalidValue (option, value);

  } else if (option == "print_fg") {
    if      (value == "true")  FactorGraph::enablePrintFactorGraph();
    else if (value == "false") FactorGraph::disablePrintFactorGraph();
    else                       returnVal = invalidValue (option, value);

  } else {
    std::cerr << "Warning: invalid option `" << option << "'" << std::endl;
    returnVal = false;
  }
  return returnVal;
}



void
printHeader (std::string header, std::ostream& os)
{
  printAsteriskLine (os);
  os << header << std::endl;
  printAsteriskLine (os);
}



void
printSubHeader (std::string header, std::ostream& os)
{
  printDashedLine (os);
  os << header << std::endl;
  printDashedLine (os);
}



void
printAsteriskLine (std::ostream& os)
{
  os << "********************************" ;
  os << "********************************" ;
  os << std::endl;
}



void
printDashedLine (std::ostream& os)
{
  os << "--------------------------------" ;
  os << "--------------------------------" ;
  os << std::endl;
}

}  // namespace Util



namespace log_aware {

void
normalize (Params& v)
{
  if (globals::logDomain) {
    double sum = std::accumulate (v.begin(), v.end(),
        log_aware::addIdenty(), util::logSum);
    assert (sum != -std::numeric_limits<double>::infinity());
    v -= sum;
  } else {
    double sum = std::accumulate (v.begin(), v.end(), 0.0);
    assert (sum != 0.0);
    v /= sum;
  }
}



double
getL1Distance (const Params& v1, const Params& v2)
{
  assert (v1.size() == v2.size());
  double dist = 0.0;
  if (globals::logDomain) {
    dist = std::inner_product (v1.begin(), v1.end(), v2.begin(), 0.0,
        std::plus<double>(), FuncObject::abs_diff_exp<double>());
  } else {
    dist = std::inner_product (v1.begin(), v1.end(), v2.begin(), 0.0,
        std::plus<double>(), FuncObject::abs_diff<double>());
  }
  return dist;
}



double
getMaxNorm (const Params& v1, const Params& v2)
{
  assert (v1.size() == v2.size());
  double max = 0.0;
  if (globals::logDomain) {
    max = std::inner_product (v1.begin(), v1.end(), v2.begin(), 0.0,
        FuncObject::max<double>(), FuncObject::abs_diff_exp<double>());
  } else {
    max = std::inner_product (v1.begin(), v1.end(), v2.begin(), 0.0,
        FuncObject::max<double>(), FuncObject::abs_diff<double>());
  }
  return max;
}



double
pow (double base, unsigned iexp)
{
  return globals::logDomain
      ? base * iexp
      : std::pow (base, iexp);
}



double
pow (double base, double exp)
{
  // `expoent' should not be in log domain
  return globals::logDomain
      ? base * exp
      : std::pow (base, exp);
}



void
pow (Params& v, unsigned iexp)
{
  if (iexp == 1) {
    return;
  }
  globals::logDomain ? v *= iexp : v ^= (int)iexp;
}



void
pow (Params& v, double exp)
{
  // `expoent' should not be in log domain
  globals::logDomain ? v *= exp : v ^= exp;
}

}  // namespace log_aware

}  // namespace horus


