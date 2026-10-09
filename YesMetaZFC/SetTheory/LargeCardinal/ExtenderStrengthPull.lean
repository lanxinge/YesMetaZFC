import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedCode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderExactStrength

/-! # 最大强度的实际有界证书及外层回拉

给定两个真实有限列空间后，原有界超幂、全部代表和缺失子集由同一有界
公式刻画。外层初等图因而可反射完整最大强度，而非只保留支撑以下的覆盖。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ex_strength0_m {d} (ω κ L X F K H : Term d) : Formula 1 d := set[d] ⟪
  ⌜ω⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜L⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜F⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜KP.ord0_m⌝ₚ(⌜L⌝ₛ) ∧ ⌜K⌝ₛ ∈ ⌜X⌝ₛ ∧
  (∃ P ∈ ⌜X⌝ₛ, ∃ A ∈ ⌜X⌝ₛ, ∃ Q ∈ ⌜X⌝ₛ, ∃ Y ∈ ⌜X⌝ₛ, ∃ e ∈ ⌜X⌝ₛ,
    ⌜FilterZF.source_m⌝ₚ(⌜X⌝ₛ, ⌜κ⌝ₛ, P) ∧ ⌜eb_collapse_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜K⌝ₛ, ⌜X⌝ₛ, P, ⌜F⌝ₛ, A, Q, Y, e, ⌜H⌝ₛ) ∧
    ⌜es_strength0_m⌝ₚ(⌜X⌝ₛ, ⌜L⌝ₛ, Y))⟫
derive_free_closed ex_strength0_m

theorem ex_strength0_delta_l {d} (ω κ L X F K H : Term d) : (ex_strength0_m ω κ L X F K H).IsDelta0 := by
  unfold ex_strength0_m
  repeat first
    | exact KP.ord0_delta_l .. | exact FilterZF.source_delta_l .. | exact eb_collapse_delta_l ..
    | exact es_strength0_delta_l .. | exact .mem ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.existsMem

theorem ex_strength0_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω κ L X F K H : Term d)
    (sk : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) (K.eval ρ))
    (sl : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (L.eval ρ) (H.eval ρ)) :
    Formula.satisfies ρ (ex_strength0_m ω κ L X F K H) ↔
      Ex_strength_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) := by
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken
  have collapse (P A Q Y e : M.Domain) :
      Formula.satisfies (((((ρ.push P).push A).push Q).push Y).push e)
        (eb_collapse_m (w ω) (w κ) (w L) (w K) (w X) Term.newest.weaken.weaken.weaken.weaken (w F)
          Term.newest.weaken.weaken.weaken Term.newest.weaken.weaken Term.newest.weaken .newest (w H)) ↔
        Eb_collapse_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (X.eval ρ) P (F.eval ρ) A Q Y e := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      (eb_collapse_sat_l (ZF.modelsKP hZF) (((((ρ.push P).push A).push Q).push Y).push e)
        (w ω) (w κ) (w L) (w K) (w X) Term.newest.weaken.weaken.weaken.weaken (w F)
        Term.newest.weaken.weaken.weaken Term.newest.weaken.weaken Term.newest.weaken .newest (w H)
        (by simpa only [w, Definitional.Term.eval_weaken] using sl))
  dsimp only [w] at collapse
  simp only [ex_strength0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF), Formula.satisfies_existsMem_iff, FilterZF.source_sat_l,
    collapse, es_strength0_sat_l, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hw, hk, hl, hf, ho, hK, P, hP, A, _, Q, _, Y, hY, e, _, power, col, strength⟩
    exact ⟨hw, hk, hl, hf, ho, K.eval ρ, P, A, Q, Y, e, hK, hP, hY, sk, power, col, strength⟩
  · rintro ⟨hw, hk, hl, hf, ho, K₀, P, A, Q, Y, e, hK, hP, hY, seq, power, col, strength⟩
    have eq := hZF.1.eq_of_same_members K₀ (K.eval ρ) fun f => (seq f).trans (sk f).symm
    subst K₀
    have owned : M.mem A (X.eval ρ) ∧ M.mem Q (X.eval ρ) ∧ M.mem e (X.eval ρ) := by
      obtain ⟨_, _, _, _, _, pool, _, _, _, hQ, he, _⟩ := col
      exact ⟨pool.carrier, hQ, he⟩
    exact ⟨hw, hk, hl, hf, ho, hK, P, hP, A, owned.1, Q, owned.2.1, Y, hY, e, owned.2.2, power, col, strength⟩

theorem Ex_strength_d.pull_l (hZF : M.Models ZF) {ω B R b U S u π X P K Y κ κ' L L' F F' : M.Domain}
    (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d (kp_pair_l (ZF.modelsKP hZF)) b B R) (mu : Smem_d (kp_pair_l (ZF.modelsKP hZF)) u U S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω b u B U π)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω U S) (hωB : M.mem ω B)
    (source : Ep_source_d hZF ω ω K X P) (hXY : Rd_entry_d X Y π)
    (hκ : Rd_entry_d κ κ' π) (hL : Rd_entry_d L L' π) (hF : Rd_entry_d F F' π)
    (big : Ex_strength_d hZF ω κ' L' Y F') : Ex_strength_d hZF ω κ L X F := by
  have hωπ := hj.omega_l _ hZF source.omega bt ut mb mu hωB
  have own x (hx : M.mem x X) := bt X (hj.1.1.input_mem_of_pairMember hXY) x hx
  obtain ⟨D, hD, sd⟩ := source.sequences.space κ ((hj.member_l _ hZF source.omega mb mu hκ hXY).mpr big.2.1)
  obtain ⟨H, hH, sh⟩ := source.sequences.space L ((hj.member_l _ hZF source.omega mb mu hL hXY).mpr big.2.2.1)
  obtain ⟨D', _, hDD⟩ := hj.1.1.2.2 D (own D hD)
  obtain ⟨H', _, hHH⟩ := hj.1.1.2.2 H (own H hH)
  have sd' := hj.sequences_l hZF source.omega bt ut mb mu theory hωB hκ hDD sd
  have sh' := hj.sequences_l hZF source.omega bt ut mb mu theory hωB hL hHH sh
  let ρ : Env M 7 := ⟨Fin.cases H (Fin.cases D (Fin.cases F (Fin.cases X (Fin.cases L (Fin.cases κ (fun _ => ω)))))), fun _ => ω⟩
  let η : Env M 7 := ⟨Fin.cases H' (Fin.cases D' (Fin.cases F' (Fin.cases Y (Fin.cases L' (Fin.cases κ' (fun _ => ω)))))), fun _ => ω⟩
  have tr := smap_delta_l _ hZF source.omega bt ut mb mu hj
    (ex_strength0_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
    (by simp -implicitDefEqProofs) (ex_strength0_delta_l ..) ρ η
    (Fin.cases hHH (Fin.cases hDD (Fin.cases hF (Fin.cases hXY (Fin.cases hL (Fin.cases hκ (fun _ => hωπ)))))))
  exact (ex_strength0_sat_l hZF ρ (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) sd sh).mp
    (tr.mpr ((ex_strength0_sat_l hZF η (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) sd' sh').mpr big))

end YesMetaZFC.SetTheory.LargeCardinal
