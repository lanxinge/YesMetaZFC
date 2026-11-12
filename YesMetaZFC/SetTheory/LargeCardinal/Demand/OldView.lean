import YesMetaZFC.SetTheory.LargeCardinal.Types.CandidateModel
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Parameters

/-! # 旧 demanding 回合的共同层视图

输入是已完成的六十二槽原回合及两侧实际数字坐标。语言、原类型、弹性
与双图元数均从这一回合读取，并由同一共同图产生当前模型中的十五个像。
历史事件本身不要求落在低秩段内，事件与此视图的对应由调用处另行核对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.demand_view_l
    {Ω b B R₀ c X R d Y S j k w₀ z₀ z w' z' L l U V Γ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (zx : (smdl_structure_l I (R := R) mx.2.1).Models ZF)
    (hZY : (smdl_structure_l I (R := S) my.2.1).Models ZFC)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k) (ext : Rf_ext_d I B R₀)
    (root : Rr_layer_d I Ω B R₀ w₀ z₀)
    (ρ : Env (smdl_structure_l I (R := R) mx.2.1) 62)
    (round : Formula.satisfies ρ td_round0_m)
    (source : Rr_layer_d I Ω X R (ρ.bound 19).val z)
    (target : Rr_layer_d I Ω Y S w' z') (below : Rd_entry_d (ρ.bound 0).val L R) :
    let Yn := smdl_structure_l I (R := S) my.2.1
    ∃ θ : Env Yn 10, ∃ w j' d' q' n' : Yn.Domain,
      Formula.satisfies θ ee_language0_m ∧ (θ.bound 0).val = w' ∧
      Ee_elastic_d ⟨θ.bound 6,θ.bound 7,θ.bound 8,θ.bound 9⟩ w ∧
      Td_arity_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZY))) j' d' q' n' (θ.bound 2) ∧
      ∀ i : Fin 15, Rd_entry_d
        (ρ.bound ([19,0,9,1,2,3,12,13,14,15,4,25,26,27,28].get i)).val
        ([θ.bound 0,θ.bound 1,θ.bound 2,θ.bound 3,θ.bound 4,θ.bound 5,
          θ.bound 6,θ.bound 7,θ.bound 8,θ.bound 9,w,j',d',q',n'].get i).val t := by
  intro Yn
  let Xn := smdl_structure_l I (R := R) mx.2.1
  have zy := ZFC.models_zf_l hZY
  have hX := ZF.modelsKP zx
  have hY := ZF.modelsKP zy
  have omega := (td_round_native_l hX ρ round).1
  have parts := (Formula.satisfies_conj_iff ..).mp round |>.2
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff] at parts
  obtain ⟨_,_,_,_,_,_,language,type,elastic,_,record,_⟩ := parts
  have type := (tt_realized_sat_l (kp_pair_l hX) hX ..).mp type
  have elastic := (ee_elastic_sat_l ..).mp elastic
  have record := (td_record_sat_l (kp_pair_l hX) hX.1 ..).mp record
  let a : Env Xn 10 := ρ.reindex (fun i => [19,0,9,1,2,3,12,13,14,15].get i)
  have valid : Formula.satisfies a ee_language0_m := by
    exact (Formula.closed_env_l ee_language0_m ee_language0_closed_l (by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (fun i => Fin.elim0 i)))))))))) i)).mp
      ((Formula.satisfies_bind ..).mp language)
  let Un : Xn.Domain := ⟨U,common.left_rank.2.1⟩
  have rank := (rr_rank_native_l I mx.2.1 hX (⟨L,common.left_rank.1⟩ : Xn.Domain) Un).mp common.left_rank
  have hk : Xn.mem (ρ.bound 0) Un := KP.v_ordinal_subset_l hX rank _ below
  obtain ⟨low,θ,points,hw,language'⟩ :=
    common.language_model_l hZF hΩ mb mx my zx hZY left right ext root source target a rfl hk valid
  -- 原类型是同一完整查询池的子集，故也属于共同秩层。
  have typeLow : Xn.mem (ρ.bound 4) Un :=
    v_subset_mem_l (kp_pair_l hX) rank (low 5) (fun x hx => ((type.truth x).mp hx).1)
  have hn : Xn.mem (ρ.bound 28) (ρ.bound 19) :=
    omega.transitive hX _ record.finite _ record.height_end.predecessor_mem
  have hq : Xn.mem (ρ.bound 27) (ρ.bound 19) :=
    omega.transitive hX _ hn _ record.pending_end.predecessor_mem
  have hd : Xn.mem (ρ.bound 26) (ρ.bound 19) :=
    omega.transitive hX _ hq _ record.labels_end.predecessor_mem
  have hj : Xn.mem (ρ.bound 25) (ρ.bound 19) := by
    have ord : Xn.IsOrdinal (ρ.bound 25) := record.twice.elim (fun _ h => h.1.1.1)
    rcases ZF.ordinalAddition_left_eq_or_mem zx (kp_pair_l hX) ord record.twice with eq | lt
    · change ρ.bound 25 = ρ.bound 26 at eq
      exact eq.symm ▸ hd
    · exact omega.transitive hX _ hd _ lt
  let ix : Fin 5 → Fin 62 := fun i => [4,25,26,27,28].get i
  have bound : ∀ i, Xn.mem (ρ.bound (ix i)) Un :=
    Fin.cases typeLow (Fin.cases (v_transitive_l (kp_pair_l hX) rank _ (low 0) _ hj)
      (Fin.cases (v_transitive_l (kp_pair_l hX) rank _ (low 0) _ hd)
        (Fin.cases (v_transitive_l (kp_pair_l hX) rank _ (low 0) _ hq)
          (Fin.cases (v_transitive_l (kp_pair_l hX) rank _ (low 0) _ hn) (fun i => Fin.elim0 i)))))
  have values i : ∃ y : Yn.Domain, Rd_entry_d (ρ.bound (ix i)).val y.val t := by
    obtain ⟨y,hy,xy⟩ := common.injection.1.2.2 (ρ.bound (ix i)).val
      ((common.carrier _).mpr ⟨(ρ.bound _).property,bound i⟩)
    exact ⟨⟨y,hy⟩,xy⟩
  obtain ⟨v,images⟩ := Classical.axiomOfChoice values
  have mem (i : Fin 10) (h : Xn.mem (a.bound i) (ρ.bound 4)) :
      Yn.mem (θ.bound i) (v 0) := (common.pred _ _ (images 0) _).mpr ⟨_,h,points i⟩
  have elastic' : Ee_elastic_d ⟨θ.bound 6,θ.bound 7,θ.bound 8,θ.bound 9⟩ (v 0) :=
    ⟨⟨mem 6 elastic.1.1,mem 7 elastic.1.2⟩,mem 8 elastic.2.1,mem 9 elastic.2.2⟩
  let α : Env Xn 5 := ρ.reindex (fun i => [25,26,27,28,9].get i)
  let β : Env Yn 5 := ⟨fun i => [v 1,v 2,v 3,v 4,θ.bound 2].get i,θ.free⟩
  have links : ∀ i, Rd_entry_d (α.bound i).val (β.bound i).val t :=
    Fin.cases (images 1) (Fin.cases (images 2) (Fin.cases (images 3)
      (Fin.cases (images 4) (Fin.cases (points 2) (fun i => Fin.elim0 i)))))
  have finite : ∀ i, Xn.mem (α.bound i) (ρ.bound 19) :=
    Fin.cases hj (Fin.cases hd (Fin.cases hq (Fin.cases hn (Fin.cases record.finite (fun i => Fin.elim0 i)))))
  have digits := common.layer_image_l (ZF.modelsKP hZF) mx.2.1
    (right.extensional_l hZF hΩ mb my ext) source target (v_transitive_l (kp_pair_l hX) rank) (low 0)
  have arity : Td_arity_d (kp_pair_l hX) (α.bound 0) (α.bound 1) (α.bound 2) (α.bound 3) (α.bound 4) :=
    ⟨record.twice,record.labels_end,record.pending_end,record.height_end⟩
  -- 加法不是有界公式；五个有限元数通过共同根传输其完整定义。
  have moved := (smap_numeric_model_peer_l hZF hΩ mb mx my left right ext
    (left.extensional_l hZF hΩ mb mx ext) (right.extensional_l hZF hΩ mb my ext) root source target
    (td_arity_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4))
    (by simp -implicitDefEqProofs) α β (fun i => by
      obtain ⟨n,_,hn⟩ := (source.image _).mp (finite i)
      exact Or.inr ⟨n,hn,(digits.2 n _).mpr ⟨_,hn,links i⟩⟩)).mp
        ((td_arity_sat_l (kp_pair_l hX) hX.1 α (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mpr arity)
  refine ⟨θ,v 0,v 1,v 2,v 3,v 4,language',hw,elastic',
    (td_arity_sat_l (kp_pair_l hY) hY.1 β (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mp moved,?_⟩
  exact Fin.cases (points 0) (Fin.cases (points 1) (Fin.cases (points 2) (Fin.cases (points 3)
    (Fin.cases (points 4) (Fin.cases (points 5) (Fin.cases (points 6) (Fin.cases (points 7)
      (Fin.cases (points 8) (Fin.cases (points 9) (Fin.cases (images 0) (Fin.cases (images 1)
        (Fin.cases (images 2) (Fin.cases (images 3) (Fin.cases (images 4) (fun i => Fin.elim0 i)))))))))))))))

end YesMetaZFC.SetTheory.LargeCardinal
