section \<open> Project Marking \<close>

theory ProjectMarking
  imports "Z_Machines.Z_Machines"
begin

type_synonym ident = string

consts Academics :: "ident set"

enumtype Status = 
  awaiting_advisor_report | awaiting_mark_sheets | 
  resolution | awaiting_feedback_forms | complete

zstore ProjectState =
  status :: Status
  submitted :: "bool"
  advisor_report :: "bool"
  markers :: "ident list"
  marking_sheets :: "bool list"
  where
    "length marking_sheets \<le> length markers"

zoperation Submit =
  over ProjectState
  pre "\<not> submitted"
  update "[submitted\<Zprime> = True]"

zoperation AdvisorReport =
  over ProjectState
  pre "\<not> advisor_report"
  update "[advisor_report\<Zprime> = True]"

zoperation AssignMarkers =
  params 
    first_marker \<in> Academics 
    second_marker \<in> Academics
  pre "status = awaiting_advisor_report \<and> first_marker \<noteq> second_marker"
  update "[markers\<Zprime> = [first_marker, second_marker]]"

zoperation ToMarkingPhase =
  pre "status = awaiting_advisor_report \<and> submitted \<and> advisor_report \<and> length markers = 2"
  update "[status\<Zprime> = awaiting_mark_sheets]"

zmachine Project =
  over ProjectState
  init "[status \<leadsto> awaiting_advisor_report, submitted \<leadsto> False, advisor_report \<leadsto> False
        , markers \<leadsto> [], marking_sheets \<leadsto> []]"
  operations Submit AdvisorReport AssignMarkers ToMarkingPhase
  
animate Project
  defines Academics = "{''Simon'', ''Iain''}"

zstore ProjectSystemState =
  project :: "ident \<Zpfun> ProjectState"

zoperation SystemSubmit = 
  over ProjectSystemState
  promote Submit in project

end