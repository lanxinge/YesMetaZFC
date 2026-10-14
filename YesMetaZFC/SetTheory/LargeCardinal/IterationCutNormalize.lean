import YesMetaZFC.SetTheory.LargeCardinal.IterationCutHistory
import YesMetaZFC.Model.SetTheory.ClassChoice
import YesMetaZFC.SetTheory.LargeCardinal.IterationStepSyntax

/-! # 恒等段上的秩段保持

原下降高度在恒等段仍严格下降。下降模型递归则在恒等段保留上一个秩段；
遇到真实扩展器才使用新的原秩段。保留的高度始终不小于原高度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def It_hold_d (Q A i r : M.Domain) : Prop := ∃ c α β,
  Rd_entry_d i c Q ∧ Rd_entry_d r c Q ∧ Rd_entry_d i α A ∧ Rd_entry_d r β A ∧ (α = β ∨ M.mem α β)
private def it_hold_m {d} (Q A i r : Term d) : Formula 1 d := set[d] ⟪∃ c α β,
  ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, c, ⌜Q⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜r⌝ₛ, c, ⌜Q⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, α, ⌜A⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜r⌝ₛ, β, ⌜A⌝ₛ) ∧ (α = β ∨ α ∈ β)⟫
derive_free_closed it_hold_m
private theorem it_hold_sat_l (hE : Extensional M) {d} (η : Env M d) (Q A i r : Term d) :
    Formula.satisfies η (it_hold_m Q A i r) ↔ It_hold_d (Q.eval η) (A.eval η) (i.eval η) (r.eval η) := by
  simp only [it_hold_m, It_hold_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_cut_normalize_l {ω c T Q G E L A D o : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (cuts : It_cut_d hZF ω ω Q E A D)
    (ho : ∀ x, ¬ M.mem x o)
    (drop : ∀ i j k f α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
      Rd_entry_d k α A → Rd_entry_d j β A → ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ) :
    ∃ A' D', It_cut_d hZF ω ω Q E A' D' ∧
      (∀ α, Rd_entry_d o α A' ↔ Rd_entry_d o α A) ∧
      (∀ a, Rd_entry_d o a D' ↔ Rd_entry_d o a D) ∧
      (∀ i j p, M.SuccessorOf j i → Rd_entry_d i p E → (∀ x, ¬ M.mem x p) →
        ∀ a, Rd_entry_d i a D' ↔ Rd_entry_d j a D') ∧
      ∀ i j k f p κ ρ F α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
        Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d k α A' → Rd_entry_d j β A' →
        ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ := by
  have hw := nice.tree.omega
  have self i (hi : M.mem i ω) : It_hold_d Q A i i := by
    obtain ⟨c, hc⟩ := (nice.tree.diagram.model_domain i).mp hi
    obtain ⟨α, hα⟩ := (cuts.height_domain i).mp hi
    exact ⟨c, α, α, hc, hc, hα, hα, Or.inl rfl⟩
  let η : Env M 4 := ⟨Fin.cases ω (Fin.cases E (Fin.cases A (fun _ => Q))), fun _ => ω⟩
  let B : BinarySchema 4 := { body := it_hold_m (.bound 5) (.bound 4) (.bound 1) .newest }
  let φ : UnarySchema 6 := { body := set[7] ⟪
    (⌜(Term.newest : Term 7)⌝ₛ = ⌜(Term.bound 1 : Term 7)⌝ₛ ∧ (∃ p, ⌜rd_entry0_m⌝ₚ(⌜(Term.bound 2 : Term 7)⌝ₛ, p, ⌜(Term.bound 4 : Term 7)⌝ₛ) ∧ (∀ x, ¬ x ∈ p))) ∨
    (⌜KP.succ0_m⌝ₚ(⌜(Term.newest : Term 7)⌝ₛ, ⌜(Term.bound 2 : Term 7)⌝ₛ) ∧
      (∃ p κ ρ F, ⌜rd_entry0_m⌝ₚ(⌜(Term.bound 2 : Term 7)⌝ₛ, p, ⌜(Term.bound 4 : Term 7)⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p, κ, ρ, F)))⟫ }
  have valid i r : B.denote η i r ↔ It_hold_d Q A i r := it_hold_sat_l hZF.1 ..
  have step i r s : φ.denote ((η.push i).push r) s ↔
      (s = r ∧ ∃ p, Rd_entry_d i p E ∧ ∀ x, ¬ M.mem x p) ∨
      (M.SuccessorOf s i ∧ ∃ p κ ρ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, KP.succ0_sat_l hZF.1,
      rd_entry0_sat_l hZF.1, it_payload_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl
  have hoω := (nice.tree.diagram.model_domain o).mpr ⟨c, nice.tree.root o ho⟩
  obtain ⟨C, r, rf, r₀, rv, rs⟩ := ZFC.class_indexed_choice_l I hZFC B φ η hw ho ((valid o o).mpr (self o hoω)) (by
    intro i j a hi succ ha
    have hj := (hw.1.2 i hi).elim fun j' h => (h.1.eq hZF.1 succ) ▸ h.2
    obtain ⟨k, b, d, e, f, p, pred, hb, hd, he, hf, hp, data⟩ := nice.tree.steps i j hj succ
    rcases data with ⟨empty, eq, ec, ident⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
    · subst k e
      obtain ⟨b₀, α, β, hb₀, hab, hα, hβ, le⟩ := (valid i a).mp ha
      have eq := nice.tree.diagram.model_function.2 i b₀ b hb₀ hb
      subst b₀
      obtain ⟨δ, hδ⟩ := (cuts.height_domain j).mp hj
      obtain ⟨γ, image, lt⟩ := drop i j i f α δ succ pred hf hα hδ
      have eq := ident α γ image
      subst γ
      obtain ⟨X, R, _, mx, source⟩ := nice.tree.sources a b hab
      obtain ⟨q, hq⟩ := (cuts.code_domain a).mp ((nice.tree.diagram.model_domain a).mpr ⟨b, hab⟩)
      obtain ⟨V, _, _, hV, rank, reg, hω⟩ := cuts.ranks a b q β X R hab hq hβ mx
      have less := le.elim (fun eq => eq ▸ lt) (fun l => (source.rank_height_l hZF hV rank reg hω).2.1.transitive α l δ lt)
      exact ⟨a, (valid j a).mpr ⟨b, δ, β, he, hab, hδ, hβ, Or.inr less⟩,
        (step i a a).mpr (Or.inl ⟨rfl, p, hp, empty⟩)⟩
    · exact ⟨j, (valid j j).mpr (self j hj), (step i a j).mpr (Or.inr ⟨succ, p, κ, ρ, F, hp, pay⟩)⟩)
  have hold i a (ha : Rd_entry_d i a r) := (valid i a).mp (rv i a ha)
  have rr : M.IsSetFunctionFromTo I r ω ω := ⟨rf.1, rf.2.1, by
    intro i hi
    obtain ⟨a, _, ha⟩ := rf.2.2 i hi
    obtain ⟨b, _, _, _, hab, _⟩ := hold i a ha
    exact ⟨a, (nice.tree.diagram.model_domain a).mpr ⟨b, hab⟩, ha⟩⟩
  obtain ⟨V, vs⟩ := ZF.exists_range_of_setFunction hZF I cuts.heights cuts.height_domain
  obtain ⟨W, ws⟩ := ZF.exists_range_of_setFunction hZF I cuts.codes cuts.code_domain
  have af : M.IsSetFunctionFromTo I A ω V := ⟨cuts.heights, cuts.height_domain, fun i hi => by
    obtain ⟨a, ha⟩ := (cuts.height_domain i).mp hi
    exact ⟨a, (vs a).mpr ⟨i, ha⟩, ha⟩⟩
  have df : M.IsSetFunctionFromTo I D ω W := ⟨cuts.codes, cuts.code_domain, fun i hi => by
    obtain ⟨a, ha⟩ := (cuts.code_domain i).mp hi
    exact ⟨a, (ws a).mpr ⟨i, ha⟩, ha⟩⟩
  obtain ⟨A', af', as⟩ := ZF.exists_compositionFunction hZF I rr af
  obtain ⟨D', df', ds⟩ := ZF.exists_compositionFunction hZF I rr df
  have eq_at i a (ha : Rd_entry_d i a r) :
      (∀ β, Rd_entry_d i β A' ↔ Rd_entry_d a β A) ∧ (∀ d, Rd_entry_d i d D' ↔ Rd_entry_d a d D) := by
    have unique b (hb : Rd_entry_d i b r) := rr.1.2 i b a hb ha
    exact ⟨fun β => (as i β).trans ⟨fun ⟨_, b, hb, hβ⟩ => unique b hb ▸ hβ,
      fun hβ => ⟨rr.input_mem_of_pairMember ha, a, ha, hβ⟩⟩,
      fun d => (ds i d).trans ⟨fun ⟨_, b, hb, hd⟩ => unique b hb ▸ hd,
      fun hd => ⟨rr.input_mem_of_pairMember ha, a, ha, hd⟩⟩⟩
  have lower i a α β (ha : Rd_entry_d i a r) (hα : Rd_entry_d i α A) (hβ : Rd_entry_d a β A) : α = β ∨ M.mem α β := by
    obtain ⟨_, α₀, β₀, _, _, hα₀, hβ₀, le⟩ := hold i a ha
    exact cuts.heights.2 i α₀ α hα₀ hα ▸ cuts.heights.2 a β₀ β hβ₀ hβ ▸ le
  have cut i b d β X R (hb : Rd_entry_d i b Q) (hd : Rd_entry_d i d D') (hβ : Rd_entry_d i β A') (mx : Smem_d I b X R) :
      ∃ V S, Smem_d I d V S ∧ M.mem V X ∧ Vr_d X β V ∧ Sc_regular_d X β ∧ M.mem ω V := by
    obtain ⟨a, _, ha⟩ := rr.2.2 i (df'.input_mem_of_pairMember hd)
    obtain ⟨b₀, _, _, hb₀, hab, _⟩ := hold i a ha
    have eq := nice.tree.diagram.model_function.2 i b₀ b hb₀ hb
    exact cuts.ranks a b d β X R (eq ▸ hab) ((eq_at i a ha).2 d |>.mp hd) ((eq_at i a ha).1 β |>.mp hβ) mx
  have enlarge i d X R (hd : Rd_entry_d i d D') (mx : Smem_d I d X R) :
      ∃ e Y S, Rd_entry_d i e D ∧ Smem_d I e Y S ∧ M.MemberSubset Y X := by
    have hi := df'.input_mem_of_pairMember hd
    obtain ⟨b, hb⟩ := (nice.tree.diagram.model_domain i).mp hi
    obtain ⟨Z, T, _, mz, sz⟩ := nice.tree.sources i b hb
    obtain ⟨α, hα⟩ := (cuts.height_domain i).mp hi
    obtain ⟨e, he⟩ := (cuts.code_domain i).mp hi
    obtain ⟨Y, S, my, hY, ry, gy, hyω⟩ := cuts.ranks i b e α Z T hb he hα mz
    obtain ⟨β, _, hβ⟩ := af'.2.2 i hi
    obtain ⟨X₀, R₀, mx₀, hX, rx, gx, hxω⟩ := cut i b d β Z T hb hd hβ mz
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx₀.1 mx.1
    obtain ⟨a, _, ha⟩ := rr.2.2 i hi
    rcases lower i a α β ha hα (((eq_at i a ha).1 β).mp hβ) with eq | lt
    · exact ⟨e, Y, S, he, my, (ry.unique_l hZF sz.transitive hY hX (eq.symm ▸ rx)) ▸ fun _ h => h⟩
    · exact ⟨e, Y, S, he, my, (rx.compare_l hZF sz.transitive hX hY ry ((sz.rank_height_l hZF hX rx gx hxω).2.1.transitive α lt)).1⟩
  refine ⟨A', D', ⟨af'.1, af'.2.1, df'.1, df'.2.1, cut, ?_, ?_⟩, (eq_at o o r₀).1, (eq_at o o r₀).2, ?_, ?_⟩
  · intro i p κ ρ F d X R hp pay hd mx
    obtain ⟨e, Y, S, he, my, sub⟩ := enlarge i d X R hd mx
    obtain ⟨hρ, hF⟩ := cuts.contains i p κ ρ F e Y S hp pay he my
    exact ⟨sub ρ hρ, sub F hF⟩
  · intro i j p κ ρ F d X R succ hp pay hd mx
    obtain ⟨e, Y, S, he, my, sub⟩ := enlarge j d X R hd mx
    exact sub ρ (cuts.next i j p κ ρ F e Y S succ hp pay he my)
  · intro i j p succ hp empty d
    have hj := (nice.tree.move_domain i).mp ⟨p, hp⟩ |>.elim fun j' h => (h.2.eq hZF.1 succ) ▸ h.1
    obtain ⟨a, _, ha⟩ := rr.2.2 i (hw.transitive hZF j hj i succ.predecessor_mem)
    obtain ⟨b, _, hb⟩ := rr.2.2 j hj
    rcases (step i a b).mp (rs i j a b succ ha hb) with ⟨eq, _⟩ | ⟨_, q, κ, ρ, F, hq, pay⟩
    · exact ((eq_at i a ha).2 d).trans (eq ▸ (eq_at j b hb).2 d).symm
    · have eq := nice.tree.move_function.2 i q p hq hp
      obtain ⟨t, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
      exact (empty u ((pair u).mpr (Or.inl rfl))).elim
  · intro i j k f p κ ρ F α β succ pred hf hp pay hα hβ
    have hk := af'.input_mem_of_pairMember hα
    have hj := af'.input_mem_of_pairMember hβ
    obtain ⟨a, _, ha⟩ := rr.2.2 i (hw.transitive hZF j hj i succ.predecessor_mem)
    obtain ⟨b, _, hb⟩ := rr.2.2 j hj
    have eq : b = j := by
      rcases (step i a b).mp (rs i j a b succ ha hb) with ⟨_, q, hq, empty⟩ | ⟨sb, _⟩
      · have eq := nice.tree.move_function.2 i p q hp hq
        obtain ⟨t, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
        exact (empty u ((pair u).mpr (Or.inl rfl))).elim
      · exact sb.eq hZF.1 succ
    subst b
    obtain ⟨α₀, hα₀⟩ := (cuts.height_domain k).mp hk
    obtain ⟨γ₀, image₀, lt⟩ := drop i j k f α₀ β succ pred hf hα₀ (((eq_at j j hb).1 β).mp hβ)
    obtain ⟨b, hbQ⟩ := (nice.tree.diagram.model_domain k).mp hk
    obtain ⟨d, hdQ⟩ := (nice.tree.diagram.model_domain j).mp hj
    obtain ⟨X, R, _, mx, sx⟩ := nice.tree.sources k b hbQ
    obtain ⟨Y, S, _, my, sy⟩ := nice.tree.sources j d hdQ
    obtain ⟨a, _, hka⟩ := rr.2.2 k hk
    obtain ⟨q, _, hq⟩ := df'.2.2 k hk
    obtain ⟨V, _, _, hV, rank, reg, hvω⟩ := cut k b q α X R hbQ hq hα mx
    have ord := sx.rank_height_l hZF hV rank reg hvω
    have em := nice.tree.diagram.elementary k j f b X R d Y S hf hbQ hdQ mx.1 my.1
    obtain ⟨γ, _, image⟩ := em.1.1.2.2 α ord.1
    refine ⟨γ, image, ?_⟩
    rcases lower k a α₀ α hka hα₀ (((eq_at k a hka).1 α).mp hα) with eq | less
    · exact em.1.1.1.2 α γ₀ γ (eq ▸ image₀) image ▸ lt
    · exact (em.ordinal_l hZF hw sx.transitive sy.transitive mx my image ord.2.1).transitive γ₀
        ((em.member_l I hZF hw mx my image₀ image).mp less) β lt

end YesMetaZFC.SetTheory.LargeCardinal
