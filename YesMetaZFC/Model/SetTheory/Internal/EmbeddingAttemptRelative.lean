import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttemptSyntax
import YesMetaZFC.Model.SetTheory.Internal.SeparationSource

/-! # 尝试公式在传递源中的读取

程序与真值表的矩阵均为 Δ₀。外层无界量词保留为源内对象量词，
不把源的任意公式真值误当成背景真值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def At_relative_d (hKP : M.Models KP) (Z ω A R B S e n p Q J K : M.Domain) : Prop :=
  ∀ b l L F, M.mem b Z → M.mem l Z → M.mem L Z → M.mem F Z → Fb_program_d hKP ω b l L F →
    ∃ E D C H C' H', M.mem E Z ∧ M.mem D Z ∧ M.mem C Z ∧ M.mem H Z ∧ M.mem C' Z ∧ M.mem H' Z ∧
      At_cert_d hKP ω A R B S e n p Q J K b l L F E D C H C' H'

theorem at_relative_sat_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x : M.Domain // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d)
    (ω A R B S e n p Q J K : Term d) :
    Formula.satisfies ρ (at_elementary_m ω A R B S e n p Q J K) ↔ At_relative_d hKP Z
      (ω.eval ρ).val (A.eval ρ).val (R.eval ρ).val (B.eval ρ).val (S.eval ρ).val (e.eval ρ).val
      (n.eval ρ).val (p.eval ρ).val (Q.eval ρ).val (J.eval ρ).val (K.eval ρ).val := by
  have prog {a} (η : Env (rt_model_l Z hz) a) (ω b l L F : Term a) :
      Formula.satisfies η (fb_program_m ω b l L F) ↔ Fb_program_d hKP
        (ω.eval η).val (b.eval η).val (l.eval η).val (L.eval η).val (F.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ hz (fb_program_delta_l ω b l L F) η).trans (fb_program_sat_l hKP ..)
  have cert {a} (η : Env (rt_model_l Z hz) a) (ω A R B S e n p Q J K b l L F E D C H C' H' : Term a) :
      Formula.satisfies η (at_cert_m ω A R B S e n p Q J K b l L F E D C H C' H') ↔ At_cert_d hKP
        (ω.eval η).val (A.eval η).val (R.eval η).val (B.eval η).val (S.eval η).val (e.eval η).val
        (n.eval η).val (p.eval η).val (Q.eval η).val (J.eval η).val (K.eval η).val
        (b.eval η).val (l.eval η).val (L.eval η).val (F.eval η).val (E.eval η).val (D.eval η).val
        (C.eval η).val (H.eval η).val (C'.eval η).val (H'.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ hz (at_cert_delta_l ω A R B S e n p Q J K b l L F E D C H C' H') η).trans (at_cert_sat_l hKP ..)
  simp only [at_elementary_m, at_witness_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, prog, cert, Definitional.Term.eval_weaken]
  constructor
  · intro h b l L F hb hl hL hF hp
    obtain ⟨E, D, C, H, C', H', cert⟩ := h ⟨b, hb⟩ ⟨l, hl⟩ ⟨L, hL⟩ ⟨F, hF⟩ hp
    exact ⟨E.val, D.val, C.val, H.val, C'.val, H'.val,
      E.property, D.property, C.property, H.property, C'.property, H'.property, cert⟩
  · intro h b l L F hp
    obtain ⟨E, D, C, H, C', H', hE, hD, hC, hH, hC', hH', cert⟩ :=
      h b.val l.val L.val F.val b.property l.property L.property F.property hp
    exact ⟨⟨E, hE⟩, ⟨D, hD⟩, ⟨C, hC⟩, ⟨H, hH⟩, ⟨C', hC'⟩, ⟨H', hH'⟩, cert⟩

theorem at_node_relative_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x : M.Domain // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d)
    (ω A R B S e τ p Q J K : Term d) : Formula.satisfies ρ (at_node_m ω A R B S e τ p Q J K) ↔
    ∃ n, M.mem n (ω.eval ρ).val ∧ Fn0_d n (B.eval ρ).val (p.eval ρ).val ∧
      At_coherent_d n (A.eval ρ).val (B.eval ρ).val (e.eval ρ).val (p.eval ρ).val ∧
      At_prescribed_d n (A.eval ρ).val (B.eval ρ).val (e.eval ρ).val (τ.eval ρ).val (p.eval ρ).val ∧
      At_relative_d hKP Z (ω.eval ρ).val (A.eval ρ).val (R.eval ρ).val (B.eval ρ).val (S.eval ρ).val
        (e.eval ρ).val n (p.eval ρ).val (Q.eval ρ).val (J.eval ρ).val (K.eval ρ).val := by
  have basic (n : (rt_model_l Z hz).Domain) :
      Formula.satisfies (ρ.push n) (.conj (fn0_m .newest B.weaken p.weaken)
        (.conj (at_coherent_m .newest A.weaken B.weaken e.weaken p.weaken)
          (at_prescribed_m .newest A.weaken B.weaken e.weaken τ.weaken p.weaken))) ↔
        Fn0_d n.val (B.eval ρ).val (p.eval ρ).val ∧
          At_coherent_d n.val (A.eval ρ).val (B.eval ρ).val (e.eval ρ).val (p.eval ρ).val ∧
          At_prescribed_d n.val (A.eval ρ).val (B.eval ρ).val (e.eval ρ).val (τ.eval ρ).val (p.eval ρ).val := by
    have h := rt_model_delta_l hZ hz (.conj (fn0_delta_l .newest B.weaken p.weaken)
      (.conj (at_coherent_delta_l .newest A.weaken B.weaken e.weaken p.weaken)
        (at_prescribed_delta_l .newest A.weaken B.weaken e.weaken τ.weaken p.weaken))) (ρ.push n)
    simpa only [Formula.satisfies_conj_iff, fn0_sat_l hKP.1, at_coherent_sat_l hKP.1,
      at_prescribed_sat_l hKP.1, eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using h
  simp only [Formula.satisfies_conj_iff] at basic
  simp only [at_node_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    at_relative_sat_l hKP hZ hz, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨n, hn, hf, hc, hp, he⟩
    obtain ⟨hf, hc, hp⟩ := (basic n).mp ⟨hf, hc, hp⟩
    exact ⟨n.val, hn, hf, hc, hp, he⟩
  · rintro ⟨n, hn, hf, hc, hp, he⟩
    let v : (rt_model_l Z hz).Domain := ⟨n, hZ _ (ω.eval ρ).property n hn⟩
    obtain ⟨hf, hc, hp⟩ := (basic v).mpr ⟨hf, hc, hp⟩
    exact ⟨v, hn, hf, hc, hp, he⟩

end YesMetaZFC.SetTheory.Internal
