/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_BMC_H
#define CPROVER_CBMC_BMC_H

#include <list>
#include <map>
#include <memory>

#include <util/hash_cont.h>
#include <util/options.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>
#include <solvers/smt2/smt2_dec.h>
#include <langapi/language_ui.h>
#include <goto-symex/symex_target_equation.h>
#include <goto-programs/safety_checker.h>
#include <goto-symex/memory_model.h>

#include "symex_bmc.h"

class bmct:public safety_checkert
{
public:
  bmct(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    prop_convt& _prop_conv)
  :
    safety_checkert(ns, _message_handler),
    options(_options),
    ns(_symbol_table, new_symbol_table),
    equation(ns),
    symex_ptr(new symex_bmct(ns, new_symbol_table, equation)),
    prop_conv(_prop_conv),
    ui(ui_message_handlert::PLAIN),
    symex(*symex_ptr)
  {
    symex.constant_propagation=options.get_bool_option("propagation");
  }
 
  virtual ~bmct() { }

  // additional stuff   
  expr_listt bmc_constraints;  
  
  friend class cbmc_satt;
  friend class hw_cbmc_satt;
  friend class counterexample_beautification_greedyt;
  
  void set_ui(language_uit::uit _ui) { ui=_ui; }

  // the safety_checkert interface
  // ENHANCE: it would be reasonable to pass the goto_functions 
  //   parameter to the constructor
  virtual resultt operator()(
    const goto_functionst &goto_functions)
  {
    return run(goto_functions);
  }

protected:
  bmct(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    prop_convt& _prop_conv,
    symex_bmct *_symex_ptr):
    safety_checkert(ns, _message_handler),
    options(_options),
    ns(_symbol_table, new_symbol_table),
    equation(ns),
    symex_ptr(_symex_ptr),
    prop_conv(_prop_conv),
    ui(ui_message_handlert::PLAIN),
    symex(dynamic_cast<symex_bmct &>(*symex_ptr))
  {
    symex.constant_propagation=options.get_bool_option("propagation");
  }

  const optionst &options;  
  symbol_tablet new_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  symex_bmct *symex_ptr;
  prop_convt &prop_conv;
  std::unique_ptr<memory_model_baset> memory_model;

  // use gui format
  language_uit::uit ui;
  
  virtual decision_proceduret::resultt
    run_decision_procedure(prop_convt &prop_conv);

  // ENHANCE: goto_functions and prop_conv could be omitted    
  virtual resultt decide(
    const goto_functionst &,
    prop_convt &,
    bool show_report=true);
    
  // unwinding
  virtual void setup_unwind();
  virtual void do_unwind_module();
  void do_conversion();
  
  // run
  virtual resultt run(const goto_functionst &goto_functions);

  // decomposed run
  virtual resultt initialize();
  virtual resultt step(const goto_functionst &goto_functions);

  // functions used in run
  virtual void slice();
  virtual resultt show(const goto_functionst &goto_functions);

  virtual void show_vcc();
  virtual resultt all_properties(
    const goto_functionst &goto_functions,
    prop_convt &solver);
  virtual void show_vcc(std::ostream &out);
  virtual void show_program();
  virtual void report_success();
  virtual void report_failure();

  virtual void error_trace();
  
  bool cover(
    const goto_functionst &goto_functions,
    const std::string &criterion);

  friend class bmc_all_propertiest;
  friend class bmc_covert;

private:
  symex_bmct &symex;
};

#endif
