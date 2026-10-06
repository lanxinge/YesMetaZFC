import YesMetaZFC.Model.SetTheory.Internal.SourcePower
import YesMetaZFC.Model.SetTheory.Internal.SourceFamily
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model

/-! # 源内有界约化幂

候选函数集、值域和滤子属于源时，等价类投影与商关系也属于源。
只有收集全部源内有界函数需要相对幂集；商构造本身只用有界分离与纤维。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_map_source_l {ω c X S D Q U G : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X S) (theory : Sc_theory_d I ω X S)
    (hQ : M.mem Q X) (hU : M.mem U X) (hG : M.mem G X) (functions : ∀ f, M.mem f G → Fn0_d D Q f) :
    ∃ p C, M.mem p X ∧ M.mem C X ∧ Rp_map_d I D Q U G p C := by
  let ρ : Env M 2 := ⟨Fin.cases Q (fun _ => U), fun _ => Q⟩
  let φ : BinarySchema 2 := { body := rp_eq_m (.bound 2) (.bound 3) (.bound 1) .newest }
  obtain ⟨p, B, hp, _, fn, classes⟩ := sc_separation_function_l hZF hω hX hm theory φ
    (rp_eq_delta_l ..) ρ (Fin.cases hQ (fun _ => hU)) hG hG
  have cl f E (he : Rd_entry_d f E p) : Rp_class_d Q U G f E :=
    fun g => (classes f E he g).trans (and_congr_right fun _ => rp_eq_sat_l hZF.1 ..)
  obtain ⟨C, hC, range⟩ := sc_range_source_l hZF hω hX hm theory hp
  refine ⟨p, C, hp, hC, ⟨functions, fn0_function_l (ZF.modelsKP hZF)
    (fn.retarget_l (fun f E he => (range E).mpr ⟨f, he⟩)), range, fun f E => ⟨?_, ?_⟩⟩⟩
  · intro he
    exact ⟨(fn.bound_l he).1, cl f E he⟩
  · rintro ⟨hf, he⟩
    obtain ⟨B, _, hb⟩ := fn.2.1 f hf
    exact hZF.1.eq_of_same_members B E (fun g => (cl f B hb g).trans (he g).symm) ▸ hb

theorem rs_model_source_l {ω c X S D Q U G R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X S) (theory : Sc_theory_d I ω X S)
    (hQ : M.mem Q X) (hU : M.mem U X) (hG : M.mem G X) (hR : M.mem R X)
    (base : FilterZF.Base_d (ℳ := M) D U) (functions : ∀ f, M.mem f G → Fn0_d D Q f)
    (inhabited : ∃ f, M.mem f G) : ∃ d p C T, M.mem d X ∧ M.mem p X ∧ M.mem C X ∧ M.mem T X ∧
      Rp_model_d I D Q U R d G p C T := by
  obtain ⟨p, C, hp, hC, map⟩ := rs_map_source_l hZF hω hX hm theory hQ hU hG functions
  let ρ : Env M 5 := ⟨Fin.cases p (Fin.cases G (Fin.cases Q (Fin.cases U (fun _ => R)))), fun _ => Q⟩
  -- 所有代表元、滤子成员及函数值都有现成的源内界。
  let φ : BinarySchema 5 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
    (.conj (rd_entry0_m (.bound 1) (.bound 3) (.bound 4)) (.conj
      (rd_entry0_m .newest (.bound 2) (.bound 4))
      (Formula.existsMem (.bound 7) (Formula.forallMem .newest
        (Formula.existsMem (.bound 8) (Formula.existsMem (.bound 9)
          (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 5))
            (.conj (rd_entry0_m (.bound 2) .newest (.bound 4))
              (rd_entry0_m (.bound 1) .newest (.bound 12))))))))))) }
  have sat B E : φ.denote ρ B E ↔ ∃ f, M.mem f G ∧ ∃ g, M.mem g G ∧
      Rd_entry_d f B p ∧ Rd_entry_d g E p ∧ Rp_rel_d I Q U R f g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Rp_rel_d]; rfl
  have delta : φ.body.IsDelta0 := .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
    (.conj (rd_entry0_delta_l ..) (.existsMem _ (.forallMem _ (.existsMem _ (.existsMem _
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))))
  obtain ⟨T, hT, relation, spec⟩ := sc_relation_source_l hZF hω hX hm theory φ delta ρ
    (Fin.cases hp (Fin.cases hG (Fin.cases hQ (Fin.cases hU (fun _ => hR))))) hC hC
  obtain ⟨d, hd, code⟩ := theory.algebra.kpair_l hC hT
  obtain ⟨f, hf⟩ := inhabited
  obtain ⟨B, hb, _⟩ := map.projection.2.2 f hf
  refine ⟨d, p, C, T, hd, hp, hC, hT, ⟨map, ⟨code, ⟨B, hb⟩, relation,
    fun B E he => ⟨((spec B E).mp he).1, ((spec B E).mp he).2.1⟩⟩, fun f g B E hf hg => ?_⟩⟩
  change Rd_entry_d B E T ↔ _
  rw [spec B E, sat B E]
  constructor
  · rintro ⟨_, _, f', hfG, g', hgG, hf', hg', hfg⟩
    exact rp_rel_transport_l I base (functions f' hfG) (functions g' hgG)
      ((rp_kernel_l I hZF.1 base map hf' hf).mp rfl) ((rp_kernel_l I hZF.1 base map hg' hg).mp rfl) hfg
  · intro hfg
    exact ⟨map.projection.output_mem_of_pairMember hf, map.projection.output_mem_of_pairMember hg,
      f, map.projection.input_mem_of_pairMember hf, g, map.projection.input_mem_of_pairMember hg, hf, hg, hfg⟩

/-- 源中非空的值域给出常值代表，进而实际生成整个有界商。 -/
theorem rs_bounded_model_l {ω c X S D Q U R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X S) (theory : Sc_theory_d I ω X S) (power : Sc_power_d X)
    (hD : M.mem D X) (hQ : M.mem Q X) (hU : M.mem U X) (hR : M.mem R X)
    (base : FilterZF.Base_d (ℳ := M) D U) (inhabited : ∃ x, M.mem x Q) : ∃ G d p C T,
      M.mem G X ∧ M.mem d X ∧ M.mem p X ∧ M.mem C X ∧ M.mem T X ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D Q f) ∧ Rp_model_d I D Q U R d G p C T := by
  obtain ⟨G, hG, functions⟩ := sc_function_space_l hZF hω hX hm theory power hD hQ
  obtain ⟨x, hx⟩ := inhabited
  obtain ⟨f, A, hf, _, fn, value⟩ := sc_constant_l hZF hω hX hm theory hD (hX Q hQ x hx)
  have hfG : M.mem f G := (functions f).mpr ⟨hf, fn.retarget_l (fun a b hab => ((value a b).mp hab).2 ▸ hx)⟩
  obtain ⟨d, p, C, T, hd, hp, hC, hT, model⟩ := rs_model_source_l hZF hω hX hm theory hQ hU hG hR base
    (fun f hf => ((functions f).mp hf).2) ⟨f, hfG⟩
  exact ⟨G, d, p, C, T, hG, hd, hp, hC, hT, functions, model⟩

end YesMetaZFC.SetTheory.Internal
