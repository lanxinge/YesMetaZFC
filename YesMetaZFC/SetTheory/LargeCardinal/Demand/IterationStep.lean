import YesMetaZFC.SetTheory.LargeCardinal.Demand.IterationState

/-! # 原 II 胜策产生统一内部运行初态 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
theorem Td_game_d.iteration_start_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G J B W O Z g σ U₁ U₂ a : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Td_game_d (certificate.native_l I hZF hΩ) p A F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F J B W σ)
    (treeS : Td_tree_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂)
    (chosen : (smdl_structure_l I (R := R) certificate.model.2.1).mem a U₁)
    (separated : Td_separated_d p.S)
    (powerCount : Pc_count_d I Ω X R p.δ.val)
    (coding : ∃ P, (smdl_structure_l I (R := R) certificate.model.2.1).IsPowerSetOf P p.δ ∧
      (smdl_structure_l I (R := R) certificate.model.2.1).CardinalLessOrEqual
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) U₁ P) :
    ∃ H, ∃ ι : Env (smdl_structure_l I (R := R) certificate.model.2.1) 47,
      (∀ i : Fin 19, ι.bound (i.castAdd 28) =
        [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,H].get i) ∧
    ∃ o m T Q G₀ q A₀ D₀ V t Λ,
      (∀ x, ¬ M.mem x o) ∧
      Tg_root_cut_d I c X R p.ω.val (ι.bound 24).val V p.A.val D₀ A₀ ∧
      Td_state_d hZF (fun i => [Ω,c,o,X,R,(ι.bound 24).val,D₀,p.e.val,p.A.val,p.S.val].get i)
        (fun i => [X,R,c,q,z,o,m,T,Q,G₀,o,o,o,p.e.val,p.e.val,(ι.bound 24).val,V,t,Λ].get i)
        (fun i => (ι.bound i).val) := by
  obtain ⟨H,ι,head,issued,control,_,_,_,_,o,m,T,Q,G₀,q,A₀,D₀,V,t,
    empty,ho,succ,tree,node,edge,_,lettersRoot,treeRoot,cut,slice,wLow,aLow,height,bound,
    nums,sequence,index,archive,links,count,code⟩ :=
    game.raw_start_l hZF hΩ certificate numbers woodin win treeS alphabet chosen separated powerCount coding
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  have hN := ZF.modelsKP native
  let η := ι.reindex (fun i : Fin 19 => i.castAdd 28)
  have treeS' : Td_tree_d (kp_pair_l hN) (η.bound 0) (η.bound 6) (η.bound 7) :=
    (head 0).symm ▸ (head 6).symm ▸ (head 7).symm ▸ treeS
  have static : Formula.satisfies η td_static0_m := (td_static0_sat_l hN η).mpr
    ⟨control,treeS',(head 7).symm ▸ separated,a,(head 7).symm ▸ (alphabet.1 a).mp chosen⟩
  obtain ⟨Λ,lf,levels⟩ := it_levels_l hZF tree.move_function
  refine ⟨H,ι,head,o,m,T,Q,G₀,q,A₀,D₀,V,t,Λ,empty,cut,?_⟩
  exact ⟨ho,succ,tree,certificate.model,node,node,edge,
    (rr_truth_native_l I certificate.model.2.1 td_issued0_m td_issued0_closed_l ι.bound).mpr
      ((Formula.closed_env_l td_issued0_m td_issued0_closed_l
        (ρ := ι) (η := ⟨ι.bound,fun _ => ι.bound 0⟩) rfl).mp issued),
    (rr_truth_native_l I certificate.model.2.1 td_static0_m td_static0_closed_l η.bound).mpr
      ((Formula.closed_env_l td_static0_m td_static0_closed_l
        (ρ := η) (η := ⟨η.bound,fun _ => η.bound 0⟩) rfl).mp static),
    nums,slice,(fun _ h => h),wLow,aLow,lettersRoot,treeRoot,ho,sequence,index,bound,height,archive,links,count,code,lf,levels,
    Td_clear_d.empty_l empty,Tg_raw_critical_d.empty_l I empty,
    fun _ _ _ _ _ ⟨p,_,hp⟩ _ => (empty p hp).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 统一状态的实际两分支后继

两种回合只使用当前状态，所有新字段来自已经核验的原工厂。
静态控制沿同一偶数原边运输；新档案界由下一候选的序数性控制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem td_target_bounds_l {N : Structure.{u}} (hN : N.Models KP)
    (ψ : Env N 47) (issued : Formula.satisfies ψ td_issued0_m) {γ l : N.Domain}
    (low : N.mem γ l) (bound : N.mem l (ψ.bound 24)) :
    N.mem l (ψ.bound 5) ∧ ∀ x, N.mem x γ → N.mem x (ψ.bound 24) := by
  have state := (td_issued_sat_l (kp_pair_l hN) hN.1 ψ).mp issued
  obtain ⟨_,_,_,_,regular,_⟩ := td_issued_woodin_l hN ψ issued
  have ordinal := state.payload.2.2.2.2.2.2.2.2.1.1
  exact ⟨regular.isCardinal.1.transitive _ state.payload.2.2.1 _ bound,
    fun x hx => ordinal.transitive l bound x
      ((ordinal.mem bound).transitive γ low x hx)⟩

set_option maxHeartbeats 600000 in
theorem Td_state_d.advance_l {g : Fin 10 → M.Domain} {v : Fin 19 → M.Domain} {a : Fin 47 → M.Domain}
    {wr zr x : M.Domain} (h : Td_state_d hZF g v a)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (rootNumbers : Rr_layer_d I (g 0) (g 3) (g 4) wr zr)
    (input : M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4)) :
    ∃ w b, Td_state_d hZF g w b ∧ Td_run_step_d hZF g x v w a b := by
  classical
  have map := h.tree.diagram.elementary (g 2) (v 5) (v 3) (g 1) (g 3) (g 4)
    (v 2) (v 0) (v 1) h.origin h.root_node h.node root.model h.model
  have native := ZFC.models_zf_l ((root.map_l hZF h.tree.omega h.model map).native_l I hZF h.tree.omega)
  have hN := ZF.modelsKP native
  let N := smdl_structure_l I (R := v 1) h.model.2.1
  let ι : Env N 47 := ⟨fun i => ⟨a i,h.issued.1 i⟩,fun _ => ⟨a 0,h.issued.1 0⟩⟩
  have issued : Formula.satisfies ι td_issued0_m :=
    (rr_truth_native_l I h.model.2.1 td_issued0_m td_issued0_closed_l ι.bound).mp h.issued
  have static : Formula.satisfies (ι.reindex (fun i : Fin 19 => i.castAdd 28)) td_static0_m :=
    (rr_truth_native_l I h.model.2.1 td_static0_m td_static0_closed_l
      (fun i => ι.bound (i.castAdd 28))).mp h.static
  let χ : N.Domain := ⟨v 13,(h.model.2.2.2 _ _ h.height).1⟩
  obtain ⟨xN,hxN,ix⟩ := map.1.1.2.2 x input.1
  let z : N.Domain := ⟨xN,hxN⟩
  have hz : N.mem z (ι.bound 6) :=
    (map.relation_l I hZF h.tree.omega root.model h.model ix h.letters_root).mp input.2
  have finite {θ : M.Domain} (succ : M.SuccessorOf θ (v 6)) : M.mem θ (g 0) := by
    obtain ⟨m,sm,hm⟩ := h.tree.omega.1.2 (v 5) h.finite
    obtain ⟨n,sn,hn⟩ := h.tree.omega.1.2 (v 6) (sm.eq hZF.1 h.successor ▸ hm)
    exact sn.eq hZF.1 succ ▸ hn
  have transport {c Y S J : M.Domain} (my : Smdl_d I c Y S)
      (embed : Smap_d I (g 0) (v 2) c (v 0) Y J)
      (ι' ψ : Env (smdl_structure_l I (R := S) my.2.1) 47)
      (points : ∀ i, Rd_entry_d (a i) (ι'.bound i).val J)
      (head : ∀ i : Fin 19, ψ.bound (i.castAdd 28) = ι'.bound (i.castAdd 28)) :
      Rr_truth_d I Y S td_static0_m (fun i : Fin 19 => (ψ.bound (i.castAdd 28)).val) :=
    h.static.map_l I hZF h.tree.omega h.model my embed td_static0_closed_l
      (fun i => (congrArg Subtype.val (head i)).symm ▸ points (i.castAdd 28))
  by_cases reset : a 23 = a 1
  · obtain ⟨control,treeS,separated,z₁,letter⟩ := (td_static0_sat_l hN _).mp static
    obtain ⟨U₁,U₂,alphabet⟩ := td_alphabet_exists_l native (ι.bound 7)
    have chosen := (alphabet.1 z₁).mpr letter
    obtain ⟨θ,T₁,Q₁,G₁,E₁,j,θ₂,T₂,Q₂,G₂,E₂,c₂,P,R₂,j₂,q₂,p₂,
      succ,mid,first,node,pad,identity,next,owned,second,node₂,edge₂,move₂,root₂,_,critical,rest⟩ :=
      td_raw_reset_l hZFC root h.tree h.owned h.successor h.root_node h.node h.model h.origin ι issued
        h.letters_root h.tree_root control (Subtype.ext reset) hN
        (χn := χ) treeS alphabet chosen h.height separated h.numbers h.archive h.links h.bound
        rootNumbers h.slice h.below h.omega_low h.letters_low h.coding h.power h.round h.sequence h.index
    obtain ⟨mp,target,embed,rootMap,roots,C,γ,V,t,l,zp,slice,low,copy,ι',ε,points,issued',_,_,_,_,nums,wLow,aLow,reply⟩ := rest
    obtain ⟨b,y,b₀,H,t',ψ,m',Da',r,row,zb,hy,even,odd,pair,ending,digit,aux,value,head,valid,
      lettersRoot,treeRoot,hm',sm,seq,append,tuple,ri,rc,rX,rR,rq,zero,_,_,index,increase,bound,history,
      archive,links,rank,count,code⟩ := reply z hz
    have nativeP := ZFC.models_zf_l (target.native_l I hZF h.tree.omega)
    have hP := ZF.modelsKP nativeP
    have bounds := td_target_bounds_l hP ψ valid (γ := ⟨γ,slice.rank.1⟩)
      (l := ⟨l,(mp.2.2.2 _ _ bound).1⟩) low bound
    obtain ⟨Λ,lf,levels⟩ := it_levels_l hZF next.move_function
    let w : Fin 19 → M.Domain := fun i => [P,R₂,c₂,q₂,zp,θ,θ₂,T₂,Q₂,G₂,E₂,Da',m',l,C,γ,V,t,Λ].get i
    refine ⟨w,(fun i => (ψ.bound i).val),?_,?_⟩
    · exact ⟨finite succ,second.1,next,mp,node₂,second.2.2.1 _ _ (first.2.2.1 _ _ h.root_node),root₂,
        (rr_truth_native_l I mp.2.1 td_issued0_m td_issued0_closed_l ψ.bound).mpr
          ((Formula.closed_env_l td_issued0_m td_issued0_closed_l
            (ρ := ψ) (η := ⟨ψ.bound,fun _ => ψ.bound 0⟩) rfl).mp valid),
        transport mp embed ι' ψ points head,(congrArg Subtype.val (head 0)).symm ▸ nums,
        slice,(fun x hx => bounds.2 ⟨x,(mp.2.2.2 _ _ hx).1⟩ hx),
        (congrArg Subtype.val (head 0)).symm ▸ wLow,(congrArg Subtype.val (head 6)).symm ▸ aLow,
        lettersRoot,treeRoot,hm',seq,index,bound,bounds.1,archive,links,count,code,lf,levels,
        h.clear.step_l hZF h.links h.tree h.successor mid first second tuple ri append,critical h.critical,owned⟩
    · refine ⟨(by rw [td_copy_frame_values_l v,td_copy_frame_values_l w]; exact copy),
        v 5,T₁,Q₁,G₁,E₁,j₂,mid,first,second,edge₂,sm,?_,row,r,ri,tuple,
        ⟨j,pad,Or.inl ⟨rfl,zero⟩⟩,append⟩
      refine ⟨fun i => (ι'.bound i).val,points,fun i => congrArg Subtype.val (head i),
        H.val,t'.val,y.val,b.val,(roots.2 _ _).mpr ⟨xN,ix,zb⟩,?_⟩
      let η : Env (smdl_structure_l I (R := R₂) mp.2.1) 11 :=
        ⟨td_digit_values_d ι'.bound ψ.bound H t' y b,ψ.free⟩
      have raw := (rr_truth_native_l I mp.2.1 td_digit0_m td_digit0_closed_l η.bound).mpr
        ((Formula.closed_env_l td_digit0_m td_digit0_closed_l (ρ := η)
          (η := ⟨η.bound,fun _ => η.bound 0⟩) rfl).mp
          ((td_digit0_sat_l hP η).mpr ⟨hy,even,odd,digit,aux,value,b₀,ending⟩))
      have vals := td_digit_values_map_l Subtype.val ι'.bound ψ.bound H t' y b
      change Rr_truth_d I P R₂ td_digit0_m (fun i => (td_digit_values_d ι'.bound ψ.bound H t' y b i).val) at raw
      exact Eq.mp (congrArg (Rr_truth_d I P R₂ td_digit0_m) vals) raw
  · obtain ⟨old,selected,parent,parentRoot,ξ,κP,θ,T₁,Q₁,G₁,E₁,cP,P,S,jP,qP,pP,
      θ₂,T₂,Q₂,G₂,E₂,cH,H,RH,J,qH,pH,mid,first,node,oddEdge,_,_,next,owned,second,node₂,edge₂,_,root₂,_,critical,rest⟩ :=
      td_raw_continue_l hZFC root rootNumbers h.tree h.owned h.successor h.root_node h.node h.origin h.model ι issued
        (fun eq => reset (congrArg Subtype.val eq)) h.numbers h.slice h.omega_low h.letters_low
        h.letters_root h.tree_root h.round h.sequence h.index χ h.height h.archive h.bound h.links h.power h.coding
    obtain ⟨mh,target,embed,rootMap,roots,C,γ,V,t,l,zh,m',Da',r,row,slice,low,hm',sm,seq,append,tuple,
      ri,rc,rX,rR,rq,depth,table,growth,links,copy,ι',points,issued',nums,wLow,aLow,reply⟩ := rest
    obtain ⟨b,y,h₁,t',ψ,zb,hy,ending,even,odd,digit,aux,value,head,valid,index,lettersRoot,treeRoot,
      increase,bound,history,archive,rank,count,code⟩ := reply z hz
    have nativeH := ZFC.models_zf_l (target.native_l I hZF h.tree.omega)
    have hH := ZF.modelsKP nativeH
    have bounds := td_target_bounds_l hH ψ valid (γ := ⟨γ,slice.rank.1⟩)
      (l := ⟨l,(mh.2.2.2 _ _ bound).1⟩) low bound
    obtain ⟨Λ,lf,levels⟩ := it_levels_l hZF next.move_function
    let w : Fin 19 → M.Domain := fun i => [H,RH,cH,qH,zh,θ,θ₂,T₂,Q₂,G₂,E₂,Da',m',l,C,γ,V,t,Λ].get i
    refine ⟨w,(fun i => (ψ.bound i).val),?_,?_⟩
    · exact ⟨finite first.1,second.1,next,mh,node₂,second.2.2.1 _ _ (first.2.2.1 _ _ h.root_node),root₂,
        (rr_truth_native_l I mh.2.1 td_issued0_m td_issued0_closed_l ψ.bound).mpr
          ((Formula.closed_env_l td_issued0_m td_issued0_closed_l
            (ρ := ψ) (η := ⟨ψ.bound,fun _ => ψ.bound 0⟩) rfl).mp valid),
        transport mh embed ι' ψ points head,(congrArg Subtype.val (head 0)).symm ▸ nums,
        slice,(fun x hx => bounds.2 ⟨x,(mh.2.2.2 _ _ hx).1⟩ hx),
        (congrArg Subtype.val (head 0)).symm ▸ wLow,(congrArg Subtype.val (head 6)).symm ▸ aLow,
        lettersRoot,treeRoot,hm',seq,index,bound,bounds.1,archive,links,count,code,lf,levels,
        h.clear.step_l hZF h.links h.tree h.successor mid first second tuple ri append,critical h.critical,owned⟩
    · obtain ⟨r₀,k,hk,entry,pack⟩ := selected
      refine ⟨(by rw [td_copy_frame_values_l v,td_copy_frame_values_l w]; exact copy),
        old.i,T₁,Q₁,G₁,E₁,J,mid,first,second,edge₂,sm,?_,row,r,ri,tuple,
        ⟨jP,oddEdge,Or.inr ⟨k,r₀,old,hk,entry,pack,rfl,depth,table,rX ▸ rR ▸ growth⟩⟩,append⟩
      refine ⟨fun i => (ι'.bound i).val,points,fun i => congrArg Subtype.val (head i),
        h₁.val,t'.val,y.val,b.val,(roots.2 _ _).mpr ⟨xN,ix,zb⟩,?_⟩
      let η : Env (smdl_structure_l I (R := RH) mh.2.1) 11 :=
        ⟨td_digit_values_d ι'.bound ψ.bound h₁ t' y b,ψ.free⟩
      have raw := (rr_truth_native_l I mh.2.1 td_digit0_m td_digit0_closed_l η.bound).mpr
        ((Formula.closed_env_l td_digit0_m td_digit0_closed_l (ρ := η)
          (η := ⟨η.bound,fun _ => η.bound 0⟩) rfl).mp
          ((td_digit0_sat_l hH η).mpr ⟨hy,even,odd,digit,aux,value,ending⟩))
      have vals := td_digit_values_map_l Subtype.val ι'.bound ψ.bound h₁ t' y b
      change Rr_truth_d I H RH td_digit0_m (fun i => (td_digit_values_d ι'.bound ψ.bound h₁ t' y b i).val) at raw
      exact Eq.mp (congrArg (Rr_truth_d I H RH td_digit0_m) vals) raw

end YesMetaZFC.SetTheory.LargeCardinal
