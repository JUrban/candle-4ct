(* ========================================================================= *)
(* 4CT_candle/part2_run_cv.ml                                                *)
(*                                                                           *)
(* check_reducible cfNNN by Kernel.compute: cprsize (cfprog cfNNN) by        *)
(* birkhoff.ml's cprsize_conv, sized_check n cfNNN by cv_eval, and           *)
(* SIZED_CHECK_SOUND.  cv_config_defs lists the 633 definitions of           *)
(* configurations.ml in order; p2_cv_run lo hi checks cfLO .. cfHI and adds  *)
(* the results to p2_cv_results.                                             *)
(* ========================================================================= *)

needs "4CT/configurations.ml";;
needs "4CT_candle/part2_cv.ml";;

let cv_config_defs =
  [cf001; cf002; cf003; cf004; cf005; cf006; cf007; cf008; cf009; cf010;
   cf011; cf012; cf013; cf014; cf015; cf016; cf017; cf018; cf019; cf020;
   cf021; cf022; cf023; cf024; cf025; cf026; cf027; cf028; cf029; cf030;
   cf031; cf032; cf033; cf034; cf035; cf036; cf037; cf038; cf039; cf040;
   cf041; cf042; cf043; cf044; cf045; cf046; cf047; cf048; cf049; cf050;
   cf051; cf052; cf053; cf054; cf055; cf056; cf057; cf058; cf059; cf060;
   cf061; cf062; cf063; cf064; cf065; cf066; cf067; cf068; cf069; cf070;
   cf071; cf072; cf073; cf074; cf075; cf076; cf077; cf078; cf079; cf080;
   cf081; cf082; cf083; cf084; cf085; cf086; cf087; cf088; cf089; cf090;
   cf091; cf092; cf093; cf094; cf095; cf096; cf097; cf098; cf099; cf100;
   cf101; cf102; cf103; cf104; cf105; cf106; cf107; cf108; cf109; cf110;
   cf111; cf112; cf113; cf114; cf115; cf116; cf117; cf118; cf119; cf120;
   cf121; cf122; cf123; cf124; cf125; cf126; cf127; cf128; cf129; cf130;
   cf131; cf132; cf133; cf134; cf135; cf136; cf137; cf138; cf139; cf140;
   cf141; cf142; cf143; cf144; cf145; cf146; cf147; cf148; cf149; cf150;
   cf151; cf152; cf153; cf154; cf155; cf156; cf157; cf158; cf159; cf160;
   cf161; cf162; cf163; cf164; cf165; cf166; cf167; cf168; cf169; cf170;
   cf171; cf172; cf173; cf174; cf175; cf176; cf177; cf178; cf179; cf180;
   cf181; cf182; cf183; cf184; cf185; cf186; cf187; cf188; cf189; cf190;
   cf191; cf192; cf193; cf194; cf195; cf196; cf197; cf198; cf199; cf200;
   cf201; cf202; cf203; cf204; cf205; cf206; cf207; cf208; cf209; cf210;
   cf211; cf212; cf213; cf214; cf215; cf216; cf217; cf218; cf219; cf220;
   cf221; cf222; cf223; cf224; cf225; cf226; cf227; cf228; cf229; cf230;
   cf231; cf232; cf233; cf234; cf235; cf236; cf237; cf238; cf239; cf240;
   cf241; cf242; cf243; cf244; cf245; cf246; cf247; cf248; cf249; cf250;
   cf251; cf252; cf253; cf254; cf255; cf256; cf257; cf258; cf259; cf260;
   cf261; cf262; cf263; cf264; cf265; cf266; cf267; cf268; cf269; cf270;
   cf271; cf272; cf273; cf274; cf275; cf276; cf277; cf278; cf279; cf280;
   cf281; cf282; cf283; cf284; cf285; cf286; cf287; cf288; cf289; cf290;
   cf291; cf292; cf293; cf294; cf295; cf296; cf297; cf298; cf299; cf300;
   cf301; cf302; cf303; cf304; cf305; cf306; cf307; cf308; cf309; cf310;
   cf311; cf312; cf313; cf314; cf315; cf316; cf317; cf318; cf319; cf320;
   cf321; cf322; cf323; cf324; cf325; cf326; cf327; cf328; cf329; cf330;
   cf331; cf332; cf333; cf334; cf335; cf336; cf337; cf338; cf339; cf340;
   cf341; cf342; cf343; cf344; cf345; cf346; cf347; cf348; cf349; cf350;
   cf351; cf352; cf353; cf354; cf355; cf356; cf357; cf358; cf359; cf360;
   cf361; cf362; cf363; cf364; cf365; cf366; cf367; cf368; cf369; cf370;
   cf371; cf372; cf373; cf374; cf375; cf376; cf377; cf378; cf379; cf380;
   cf381; cf382; cf383; cf384; cf385; cf386; cf387; cf388; cf389; cf390;
   cf391; cf392; cf393; cf394; cf395; cf396; cf397; cf398; cf399; cf400;
   cf401; cf402; cf403; cf404; cf405; cf406; cf407; cf408; cf409; cf410;
   cf411; cf412; cf413; cf414; cf415; cf416; cf417; cf418; cf419; cf420;
   cf421; cf422; cf423; cf424; cf425; cf426; cf427; cf428; cf429; cf430;
   cf431; cf432; cf433; cf434; cf435; cf436; cf437; cf438; cf439; cf440;
   cf441; cf442; cf443; cf444; cf445; cf446; cf447; cf448; cf449; cf450;
   cf451; cf452; cf453; cf454; cf455; cf456; cf457; cf458; cf459; cf460;
   cf461; cf462; cf463; cf464; cf465; cf466; cf467; cf468; cf469; cf470;
   cf471; cf472; cf473; cf474; cf475; cf476; cf477; cf478; cf479; cf480;
   cf481; cf482; cf483; cf484; cf485; cf486; cf487; cf488; cf489; cf490;
   cf491; cf492; cf493; cf494; cf495; cf496; cf497; cf498; cf499; cf500;
   cf501; cf502; cf503; cf504; cf505; cf506; cf507; cf508; cf509; cf510;
   cf511; cf512; cf513; cf514; cf515; cf516; cf517; cf518; cf519; cf520;
   cf521; cf522; cf523; cf524; cf525; cf526; cf527; cf528; cf529; cf530;
   cf531; cf532; cf533; cf534; cf535; cf536; cf537; cf538; cf539; cf540;
   cf541; cf542; cf543; cf544; cf545; cf546; cf547; cf548; cf549; cf550;
   cf551; cf552; cf553; cf554; cf555; cf556; cf557; cf558; cf559; cf560;
   cf561; cf562; cf563; cf564; cf565; cf566; cf567; cf568; cf569; cf570;
   cf571; cf572; cf573; cf574; cf575; cf576; cf577; cf578; cf579; cf580;
   cf581; cf582; cf583; cf584; cf585; cf586; cf587; cf588; cf589; cf590;
   cf591; cf592; cf593; cf594; cf595; cf596; cf597; cf598; cf599; cf600;
   cf601; cf602; cf603; cf604; cf605; cf606; cf607; cf608; cf609; cf610;
   cf611; cf612; cf613; cf614; cf615; cf616; cf617; cf618; cf619; cf620;
   cf621; cf622; cf623; cf624; cf625; cf626; cf627; cf628; cf629; cf630;
   cf631; cf632; cf633];;

let cv_check_config cfdef =
  let cf = lhs (concl cfdef) and lit = rhs (concl cfdef) in
  let cp = fst (dest_pair lit) in
  let nth = cprsize_conv (mk_comb (`cprsize`, cp)) in
  let n = rhs (concl nth) in
  let ev = EQT_ELIM (cv_eval (list_mk_comb (`sized_check`, [n; lit]))) in
  let pth = TRANS (REWRITE_CONV[cfprog; cfdef; FST]
                     (mk_comb(`cprsize`, mk_comb(`cfprog`, cf)))) nth in
  let eq = MK_COMB (AP_TERM `sized_check` pth, cfdef) in
  let th = MP (SPEC cf SIZED_CHECK_SOUND) (EQ_MP (SYM eq) ev) in
  if hyp th = [] && concl th = mk_comb(`check_reducible`, cf) then th
  else failwith "cv_check_config";;

let p2_cv_results = ref ([] : (int * thm) list);;

let p2_cv_run lo hi =
  do_list (fun i ->
      if not (can (assoc i) (!p2_cv_results)) then
        let th = cv_check_config (el (i - 1) cv_config_defs) in
        (p2_cv_results := (i, th) :: !p2_cv_results;
         print_string ("P2CV: " ^ string_of_term (concl th) ^ "\n")))
    (lo -- hi);;
