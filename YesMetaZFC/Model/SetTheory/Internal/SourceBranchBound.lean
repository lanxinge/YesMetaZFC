import YesMetaZFC.Model.SetTheory.Internal.SourceBranchRelation
import YesMetaZFC.Model.SetTheory.Internal.SourceCover
import YesMetaZFC.Model.SetTheory.Internal.SourceRelation

/-! # 无枝标签关系的源内前驱封闭界

将源内传递包络 T 与 T 中三个坐标的全部标签合并。这个实际集合在标签
关系的前驱下封闭，其有界规格沿原初等嵌入保持；无枝条件仍按源真值分离。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sb_hull_d (T B : M.Domain) : Prop := M.TransitiveSet T ∧ M.MemberSubset T B ∧
  (∀ u, M.mem u B → M.mem u T ∨ ∃ A, M.mem A T ∧ ∃ R, M.mem R T ∧ ∃ x, M.mem x T ∧ Rd_triple_d u A R x) ∧
  ∀ A, M.mem A T → ∀ R, M.mem R T → ∀ x, M.mem x T → ∃ u, M.mem u B ∧ Rd_triple_d u A R x

def sb_hull_m {d} (T B : Term d) : Formula 1 d := .conj (Formula.isTransitive T) (.conj (Formula.subset T B)
  (.conj (Formula.forallMem B (.disj (.mem .newest T.weaken)
    (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken (Formula.existsMem T.weaken.weaken.weaken
      (rd_triple0_m (.bound 3) (.bound 2) (.bound 1) .newest))))))
    (Formula.forallMem T (Formula.forallMem T.weaken (Formula.forallMem T.weaken.weaken
      (Formula.existsMem B.weaken.weaken.weaken (rd_triple0_m .newest (.bound 3) (.bound 2) (.bound 1))))))))
derive_free_closed sb_hull_m

theorem sb_hull_delta_l {d} (T B : Term d) : (sb_hull_m T B).IsDelta0 := by
  refine .conj (.forallMem _ (.forallMem _ (.mem ..))) (.conj (.atom ..) (.conj ?_ ?_))
  · exact .forallMem _ (.disj (.mem ..) (.existsMem _ (.existsMem _ (.existsMem _ (rd_triple0_delta_l ..)))))
  · exact .forallMem _ (.forallMem _ (.forallMem _ (.existsMem _ (rd_triple0_delta_l ..))))

theorem sb_hull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T B : Term d) :
    Formula.satisfies ρ (sb_hull_m T B) ↔ Sb_hull_d (T.eval ρ) (B.eval ρ) := by
  simp only [sb_hull_m, Sb_hull_d, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, rd_triple0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Sb_hull_d.closed_l (hE : Extensional M) {T B A R u v : M.Domain}
    (h : Sb_hull_d T B) (hv : M.mem v B) (edge : Sb_edge_d A R u v) : M.mem u B := by
  obtain ⟨x, hx, y, _, ux, vy, _⟩ := edge
  have coords {z a b : M.Domain} (hz : M.mem z T) (pair : KPair_d M z a b) : M.mem a T ∧ M.mem b T := by
    have bound k (hk : k = a ∨ k = b) : M.mem k T := by
      obtain ⟨s, hs, hks⟩ := (kpair_union_l M pair k).mpr hk
      exact h.1 s (h.1 z hz s hs) k hks
    exact ⟨bound a (Or.inl rfl), bound b (Or.inr rfl)⟩
  have labels : M.mem A T ∧ M.mem R T := by
    rcases h.2.2.1 v hv with hv | ⟨A', ha, R', hr, x', _, vt⟩
    · obtain ⟨q, qr, vq⟩ := vy
      have aq := coords hv vq
      exact ⟨aq.1, (coords aq.2 qr).1⟩
    · obtain ⟨rfl, rfl, _⟩ := pc_triple_inj_l vt vy
      exact ⟨ha, hr⟩
  obtain ⟨w, hw, wx⟩ := h.2.2.2 A labels.1 R labels.2 x (h.1 A labels.1 x hx)
  exact pn_triple_unique_l hE wx ux ▸ hw

theorem sc_sb_hull_l (hKP : M.Models KP) {X P : M.Domain} (algebra : Sc_algebra_d X)
    (cover : Sc_cover_d X) (hP : M.mem P X) : ∃ T B, M.mem T X ∧ M.mem B X ∧ M.MemberSubset P B ∧ Sb_hull_d T B := by
  obtain ⟨T, hT, trans, sub⟩ := cover P hP
  obtain ⟨Q, hQ, tt⟩ := algebra.product T T hT hT
  obtain ⟨H, hH, tq⟩ := algebra.product T Q hT hQ
  obtain ⟨U, hU, pair⟩ := algebra.pair T H hT hH
  obtain ⟨B, hB, union⟩ := algebra.union U hU
  have bs u : M.mem u B ↔ M.mem u T ∨ ∃ A, M.mem A T ∧ ∃ R, M.mem R T ∧ ∃ x, M.mem x T ∧ Rd_triple_d u A R x := by
    constructor
    · intro hu
      obtain ⟨D, hd, hu⟩ := (union u).mp hu
      rcases (pair D).mp hd with rfl | rfl
      · exact Or.inl hu
      · obtain ⟨A, ha, q, hq, code⟩ := (tq u).mp hu
        obtain ⟨R, hr, x, hx, tuple⟩ := (tt q).mp hq
        exact Or.inr ⟨A, ha, R, hr, x, hx, q, tuple, code⟩
    · rintro (hu | ⟨A, ha, R, hr, x, hx, q, tuple, code⟩)
      · exact (union u).mpr ⟨T, (pair T).mpr (Or.inl rfl), hu⟩
      · exact (union u).mpr ⟨H, (pair H).mpr (Or.inr rfl), (tq u).mpr ⟨A, ha, q, (tt q).mpr ⟨R, hr, x, hx, tuple⟩, code⟩⟩
  refine ⟨T, B, hT, hB, fun p hp => (bs p).mpr (Or.inl (sub p hp)), trans,
    fun t ht => (bs t).mpr (Or.inl ht), fun u hu => (bs u).mp hu, fun A ha R hr x hx => ?_⟩
  obtain ⟨q, qr⟩ := (kp_pair_l hKP).total R x
  obtain ⟨u, uq⟩ := (kp_pair_l hKP).total A q
  exact ⟨u, (bs u).mpr (Or.inr ⟨A, ha, R, hr, x, hx, q, qr, uq⟩), q, qr, uq⟩

/-- 全相对公式在已有界上给出源内无枝关系；背景良基性由实际枝反射保证。 -/
theorem sc_sb_relation_l (hZF : M.Models ZF) {ω c X R B : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hωX : M.mem ω X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R) (hB : M.mem B X) :
    ∃ Q, M.mem Q X ∧ M.IsSetRelationOn (kp_pair_l (ZF.modelsKP hZF)) Q B ∧
      ∀ u v, Rd_entry_d u v Q ↔ M.mem u B ∧ M.mem v B ∧ Sb_bad_d ω X u v := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ne : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let φ : BinarySchema 0 := { body := sb_bad_m, freeClosed := sb_bad_closed_l }
  let ρ : Env (rt_model_l X ne) 0 := ⟨Fin.elim0, fun _ => ⟨ω, hωX⟩⟩
  obtain ⟨Q, hQ, rel, spec⟩ := sc_relation_relative_l hZF hω hX hm theory ne φ ρ hB
  have read (u v : (rt_model_l X ne).Domain) : φ.denote ρ u v ↔ Sb_bad_d ω X u.val v.val :=
    (smem_formula_l I hm ne sb_bad_m ((ρ.push u).push v)).trans (sb_bad_sat_l hZF hω hX hωX hm _)
  refine ⟨Q, hQ, rel, fun u v => ⟨fun huv => ?_, fun ⟨hu, hv, edge⟩ => ?_⟩⟩
  · have bounds := rel.2 u v huv
    exact ⟨bounds.1, bounds.2, (read ⟨u, hX B hB u bounds.1⟩ ⟨v, hX B hB v bounds.2⟩).mp
      ((spec ⟨u, hX B hB u bounds.1⟩ ⟨v, hX B hB v bounds.2⟩).mp huv).2.2⟩
  · exact (spec ⟨u, hX B hB u hu⟩ ⟨v, hX B hB v hv⟩).mpr ⟨hu, hv,
      (read ⟨u, hX B hB u hu⟩ ⟨v, hX B hB v hv⟩).mpr edge⟩

end YesMetaZFC.SetTheory.Internal
