import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Cone

/-! # 任意定向子结构族的实际系统与良基极限

对给定实际集合族 `J`，构造带标号并集 `(i,x)`、全部包含映射和直接极限。
取值映射的像恰为各分量之并；此无限族实例只要求有限定向性，良基性只用 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_union_l (hZF : M.Models ZF) {J X V : M.Domain}
    (hb : ∀ i, M.mem i J → M.MemberSubset i X)
    (hd : ∀ i j, M.mem i J → M.mem j J → ∃ k, M.mem k J ∧ M.MemberSubset i k ∧ M.MemberSubset j k)
    (hw : Wf_rel_d X V) : ∃ L A p T R q C S g,
      Di_system_d J L A p T R ∧ Di_wf_d A p R ∧ Di_limit_d A p T R q C S ∧ Wf_rel_d C S ∧ Fn0_d C X g ∧
      (∀ i j, Rd_entry_d i j L ↔ M.mem i J ∧ M.mem j J ∧ M.MemberSubset i j) ∧
      (∀ a, M.mem a A ↔ ∃ i, M.mem i J ∧ ∃ x, M.mem x i ∧ KPair_d M a i x) ∧
      ∀ x, (∃ B, Rd_entry_d B x g) ↔ ∃ i, M.mem i J ∧ M.mem x i := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : BinarySchema 0 := { body := Formula.subset (.bound 1) .newest }
  obtain ⟨L, _, hl⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ⟨Fin.elim0, fun _ => X⟩ J
  have ls i j : Rd_entry_d i j L ↔ M.mem i J ∧ M.mem j J ∧ M.MemberSubset i j :=
    (hl i j).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_subset_iff _ _ _)
  have ho : Di_order_d J L := ⟨fun i hi => (ls i i).mpr ⟨hi, hi, fun _ => id⟩,
    fun i j k hij hjk => (ls i k).mpr ⟨((ls i j).mp hij).1, ((ls j k).mp hjk).2.1,
      fun x hx => ((ls j k).mp hjk).2.2 x (((ls i j).mp hij).2.2 x hx)⟩,
    fun i j hij => ⟨((ls i j).mp hij).1, ((ls i j).mp hij).2.1⟩, fun i j hi hj => by
      obtain ⟨k, hk, hik, hjk⟩ := hd i j hi hj
      exact ⟨k, hk, (ls i k).mpr ⟨hi, hk, hik⟩, (ls j k).mpr ⟨hj, hk, hjk⟩⟩⟩
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I J X
  let ψ : UnarySchema 1 := { body := Formula.existsMem (.bound 1) (Formula.existsMem .newest
    (kpair_m (.bound 2) (.bound 1) .newest)) }
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF ψ ⟨fun _ => J, fun _ => X⟩ D
  have aspec a : M.mem a A ↔ ∃ i, M.mem i J ∧ ∃ x, M.mem x i ∧ KPair_d M a i x := by
    have sat : ψ.denote ⟨fun _ => J, fun _ => X⟩ a ↔ ∃ i, M.mem i J ∧ ∃ x, M.mem x i ∧ KPair_d M a i x := by
      simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair_sat_l M hZF.1]; rfl
    exact (ha a).trans ((and_congr_right fun _ => sat).trans ⟨And.right,
      fun ⟨i, hi, x, hx, hp⟩ => ⟨(hD a).mpr ⟨i, hi, x, hb i hi x hx, hp⟩, i, hi, x, hx, hp⟩⟩)
  let first : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  let second : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) .newest (.bound 1)) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => X⟩
  have fval a i : first.denote ρ a i ↔ ∃ x, KPair_d M a i x := by
    simp only [first, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  have sval a x : second.denote ρ a x ↔ ∃ i, KPair_d M a i x := by
    simp only [second, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  obtain ⟨p, hp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I first ρ (source := A) (target := J)
    (fun a ha => by
      obtain ⟨i, _, x, _, hax⟩ := (aspec a).mp ha
      exact ⟨i, (fval a i).mpr ⟨x, hax⟩⟩)
    (fun a _ i j hi hj => by
      obtain ⟨x, hx⟩ := (fval a i).mp hi
      obtain ⟨y, hy⟩ := (fval a j).mp hj
      exact (kpair_injective_l M hx hy).1)
    (fun a i ha hi => by
      obtain ⟨j, hj, x, _, hax⟩ := (aspec a).mp ha
      obtain ⟨y, hay⟩ := (fval a i).mp hi
      exact (kpair_injective_l M hax hay).1 ▸ hj)
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I second ρ (source := A) (target := X)
    (fun a ha => by
      obtain ⟨i, _, x, _, hax⟩ := (aspec a).mp ha
      exact ⟨x, (sval a x).mpr ⟨i, hax⟩⟩)
    (fun a _ x y hx hy => by
      obtain ⟨i, hi⟩ := (sval a x).mp hx
      obtain ⟨j, hj⟩ := (sval a y).mp hy
      exact (kpair_injective_l M hi hj).2)
    (fun a x ha hx => by
      obtain ⟨i, hi, y, hy, hay⟩ := (aspec a).mp ha
      obtain ⟨j, hax⟩ := (sval a x).mp hx
      exact (kpair_injective_l M hay hax).2 ▸ hb i hi y hy)
  have read a i x (hai : Rd_entry_d a i p) (hax : Rd_entry_d a x e) : KPair_d M a i x := by
    obtain ⟨y, hay⟩ := (fval a i).mp ((ps a i).mp hai).2
    obtain ⟨j, haj⟩ := (sval a x).mp ((es a x).mp hax).2
    exact (kpair_injective_l M hay haj).2 ▸ hay
  have node i x (hi : M.mem i J) (hx : M.mem x i) : ∃ a, Rd_entry_d a i p ∧ Rd_entry_d a x e := by
    obtain ⟨a, hax⟩ := I.total i x
    have ha := (aspec a).mpr ⟨i, hi, x, hx, hax⟩
    exact ⟨a, (ps a i).mpr ⟨ha, (fval a i).mpr ⟨x, hax⟩⟩, (es a x).mpr ⟨ha, (sval a x).mpr ⟨i, hax⟩⟩⟩
  have value a i x (hai : Rd_entry_d a i p) (hax : Rd_entry_d a x e) : M.mem x i := by
    obtain ⟨j, _, y, hy, hay⟩ := (aspec a).mp (hp.input_mem_of_pairMember hai)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hay (read a i x hai hax)
    exact hy
  obtain ⟨T, R, h, ts, rs⟩ := di_cone_system_l (V := V) hZF ho
    (fn0_of_function_l (ZF.modelsKP hZF) hp) (fn0_of_function_l (ZF.modelsKP hZF) he)
    (fun a b i x ha hb hax hbx => kpair_unique_l M hZF.1 (read a i x ha hax) (read b i x hb hbx))
    (fun a i j x hai hij hax => node j x ((ls i j).mp hij).2.1 (((ls i j).mp hij).2.2 x (value a i x hai hax)))
  obtain ⟨q, C, S, hq⟩ := di_limit_exists_l hZF h
  obtain ⟨g, hg, law, wf⟩ := di_cone_wf_l hZF h hq (fn0_of_function_l (ZF.modelsKP hZF) he) hw
    (fun a b x y hab hax hby => by
      obtain ⟨i, _, hai⟩ := hp.2.2 a (he.input_mem_of_pairMember hax)
      obtain ⟨j, _, hbj⟩ := hp.2.2 b (he.input_mem_of_pairMember hby)
      exact ((ts a b i j x y hai hbj hax hby).mp hab).2)
    (fun a b i x y hai hbi hax hby hab => ((rs a b i i x y hai hbi hax hby).mp hab).2)
  have wa : Wf_rel_d A R := wf_of_map_l hZF hw (fn0_of_function_l (ZF.modelsKP hZF) he) (by
    intro a b x y hab hax hby
    obtain ⟨i, hai, hbi⟩ := h.locality a b hab
    exact ((rs a b i i x y hai hbi hax hby).mp hab).2)
  refine ⟨L, A, p, T, R, q, C, S, g, h, fun _ B hB _ hn => wa B hB hn,
    hq, wf, hg, ls, aspec, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨B, hBx⟩
    obtain ⟨a, haB⟩ := (hq.range B).mp (hg.bound_l hBx).1
    obtain ⟨i, hi, hai⟩ := hp.2.2 a (hq.projection.bound_l haB).1
    obtain ⟨y, _, hay⟩ := he.2.2 a (hq.projection.bound_l haB).1
    have eq := (fn0_function_l (ZF.modelsKP hZF) hg).1.2 B y x (law a B y haB hay) hBx
    exact ⟨i, hi, eq ▸ value a i y hai hay⟩
  · rintro ⟨i, hi, hx⟩
    obtain ⟨a, hai, hax⟩ := node i x hi hx
    obtain ⟨B, _, haB⟩ := hq.projection.2.1 a (hp.input_mem_of_pairMember hai)
    exact ⟨B, law a B x haB hax⟩

/-- 全部内部子集组成的系统是可数定向判据的实际实例，无需另给分量或映射。 -/
theorem di_power_limit_l (hZF : M.Models ZF) (ω X : M.Domain) :
    ∃ J L A p T R q C S, M.IsPowerSetOf J X ∧ Di_system_d J L A p T R ∧
      Di_sigma_d ω J L ∧ Di_wf_d A p R ∧ Di_limit_d A p T R q C S ∧ Wf_rel_d C S := by
  obtain ⟨J, hJ⟩ := ZF.exists_powerSet hZF X
  obtain ⟨V, hw, _⟩ := wf_membership_l hZF X
  have hx := (hJ X).mpr (fun _ => id)
  obtain ⟨L, A, p, T, R, q, C, S, _, hs, hwA, hq, hwC, _, hl, _⟩ := di_union_l hZF
    (fun i hi => (hJ i).mp hi)
    (fun i j hi hj => ⟨X, hx, (hJ i).mp hi, (hJ j).mp hj⟩) hw
  exact ⟨J, L, A, p, T, R, q, C, S, hJ, hs,
    di_sigma_of_top_l hx (fun i hi => (hl i X).mpr ⟨hi, hx, (hJ i).mp hi⟩), hwA, hq, hwC⟩

end YesMetaZFC.SetTheory.Internal
