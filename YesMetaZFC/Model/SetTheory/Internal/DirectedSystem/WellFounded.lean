import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Limit
import YesMetaZFC.SetTheory.Collapse.RelationSequence

/-! # 直接极限的内部良基性

共同后继关系在带标号载体上的良基性与商上的良基性等价，只需 ZF。
可数定向系统的良基分量在 ZF＋DC 下有良基极限；普通有限定向性不足。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

/-- 每个内部可数指标族都有共同上界。 -/
def Di_sigma_d (ω J L : M.Domain) : Prop := ∀ f, Fn0_d ω J f →
  ∃ k, M.mem k J ∧ ∀ n i, Rd_entry_d n i f → Rd_entry_d i k L

theorem di_sigma_of_top_l {ω J L k : M.Domain} (hk : M.mem k J)
    (ht : ∀ i, M.mem i J → Rd_entry_d i k L) : Di_sigma_d ω J L :=
  fun _ hf => ⟨k, hk, fun _ _ hi => ht _ (hf.bound_l hi).2⟩

/-- 各分量的内部良基性，以同一指标的实际子集表达。 -/
def Di_wf_d (A p R : M.Domain) : Prop := ∀ i B, M.MemberSubset B A →
  (∀ x, M.mem x B → Rd_entry_d x i p) → (∃ x, M.mem x B) →
    ∃ x, M.mem x B ∧ ∀ y, M.mem y B → ¬ Rd_entry_d y x R

/-- 可数定向性把一条下降链同时送到一个分量；不对外部自然数归纳。 -/
theorem di_sigma_wf_l (hZF : M.Models ZF) {ω J L A p T R q C S : M.Domain}
    (hω : M.IsOmega ω) (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (h : Di_system_d J L A p T R) (hs : Di_sigma_d ω J L) (hw : Di_wf_d A p R)
    (hq : Di_limit_d A p T R q C S) : Wf_rel_d C S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ := ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push T).push R
  let φ : BinarySchema 3 := { body := di_rel_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨P, _, hp⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have hP x y : Rd_entry_d x y P ↔ M.mem x A ∧ M.mem y A ∧ Di_rel_d p T R x y :=
    (hp x y).trans (and_congr_right fun _ => and_congr_right fun _ => di_rel_sat_l hZF.1 _ _ _ _ _ _)
  apply (wf_quotient_l hZF hq.projection (fun B hB => (hq.range B).mp hB)
    (fun x y B D hx hy => (hq.relation x y B D hx hy).trans
      ⟨fun hxy => (hP x y).mpr ⟨(hq.projection.bound_l hx).1, (hq.projection.bound_l hy).1, hxy⟩,
        fun hxy => ((hP x y).mp hxy).2.2⟩)).mpr
  apply wf_of_no_desc_l hZF hDC
  intro f hf hd
  obtain ⟨v, hv⟩ := cp0_exists_l (ZF.modelsKP hZF) hf h.index
  obtain ⟨k, _, hk⟩ := hs v hv.1
  have bound n x (hnx : Rd_entry_d n x f) : ∃ y, Rd_entry_d y k p ∧ Rd_entry_d x y T := by
    obtain ⟨i, _, hxi⟩ := h.index.2.1 x (hf.bound_l hnx).2
    exact h.total x i k hxi (hk n i ((hv.value_l hf h.index hnx).mpr hxi))
  let ψ : UnarySchema 2 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF ψ ⟨Fin.cases k (fun _ => p), fun _ => A⟩ A
  have hB x : M.mem x B ↔ M.mem x A ∧ Rd_entry_d x k p :=
    (hb x).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)
  have wb : Wf_rel_d B R := fun Y hY hn => hw k Y (fun x hx => ((hB x).mp (hY x hx)).1)
    (fun x hx => ((hB x).mp (hY x hx)).2) hn
  let η := ((⟨fun _ => f, fun _ => f⟩ : Env M 1).push T).push B
  let χ : BinarySchema 3 := { body := .conj (.mem .newest (.bound 2)) (.existsE
    (.conj (rd_entry_m (.bound 2) .newest (.bound 5)) (rd_entry_m .newest (.bound 1) (.bound 4)))) }
  have sat n y : χ.denote η n y ↔ M.mem y B ∧ ∃ x, Rd_entry_d n x f ∧ Rd_entry_d x y T := by
    simp only [χ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, rd_entry_sat_l hZF.1]; rfl
  obtain ⟨g, hg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I χ η (source := ω) (target := B)
    (fun n hn => by
      obtain ⟨x, _, hnx⟩ := hf.2.1 n hn
      obtain ⟨y, hyk, hxy⟩ := bound n x hnx
      exact ⟨y, (sat n y).mpr ⟨(hB y).mpr ⟨(h.index.bound_l hyk).1, hyk⟩, x, hnx, hxy⟩⟩)
    (fun n _ y z hy hz => by
      obtain ⟨hyB, x, hnx, hxy⟩ := (sat n y).mp hy
      obtain ⟨hzB, x', hnx', hxz⟩ := (sat n z).mp hz
      have e := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 n x' x hnx' hnx
      exact h.unique x y z k ((hB y).mp hyB).2 ((hB z).mp hzB).2 hxy (e ▸ hxz))
    (fun n y _ hy => ((sat n y).mp hy).1)
  apply wf_no_desc_l hZF hω wb (fn0_of_function_l (ZF.modelsKP hZF) hg)
  intro n m y z hnm hny hmz
  obtain ⟨hyB, x, hnx, hxy⟩ := (sat n y).mp ((spec n y).mp hny).2
  obtain ⟨hzB, v, hmv, hvz⟩ := (sat m z).mp ((spec m z).mp hmz).2
  exact (h.rel_at_l ((hB z).mp hzB).2 ((hB y).mp hyB).2 hvz hxy).mp
    ((hP v x).mp (hd n m x v hnm hnx hmv)).2.2

/-- 相容锥的关系保持性沿泛性质下降；实际良基目标因而证明极限良基。 -/
theorem di_cone_wf_l (hZF : M.Models ZF) {J L A p T R q C S Y V f : M.Domain}
    (h : Di_system_d J L A p T R) (hq : Di_limit_d A p T R q C S)
    (hf : Fn0_d A Y f) (hw : Wf_rel_d Y V)
    (hc : ∀ x y u v, Rd_entry_d x y T → Rd_entry_d x u f → Rd_entry_d y v f → u = v)
    (hr : ∀ x y i u v, Rd_entry_d x i p → Rd_entry_d y i p →
      Rd_entry_d x u f → Rd_entry_d y v f → Rd_entry_d x y R → Rd_entry_d u v V) :
    ∃ g, Fn0_d C Y g ∧ (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y g) ∧
      Wf_rel_d C S := by
  obtain ⟨g, hg, law, rel, _⟩ := di_factor_rel_l hZF h hq hf hc hr
  exact ⟨g, hg, law, wf_of_map_l hZF hw hg rel⟩

end YesMetaZFC.SetTheory.Internal