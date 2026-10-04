import YesMetaZFC.Model.SetTheory.Internal.PointwiseTrace
import YesMetaZFC.Model.SetTheory.Internal.PointwiseDiagonal

/-! # 存在行在源中具有统一代表见证

先在源内集合 A 上选取函数值见证，再取对角并延拓到整个 D。所得代表属于
源内部函数域，且在 A 的每一点满足原存在行的量词体；全部代码可以非标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_pe_witness_l {ω c X R D E F n V r z i j b a A}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hF : Sfm_d I ω n F) (hV : Seval_d I X R E F n V) (hc : M.PairMember I r z F)
    (hs : Sop_d I 3 z i j) (hj : M.mem j n) (hb : M.mem b ω) (hB : Sbound_d I F b)
    (ha : M.mem a E) (hA : M.mem A X) (hAD : M.MemberSubset A D)
    (htot : ∀ p, M.mem p A → Pe_sat_d I b D X R E F n r a p) :
    ∃ g a', Sfun_d X D g ∧ Senv_update_d I a i g a' ∧ ∀ p, M.mem p A → Pe_sat_d I b D X R E F n j a' p := by
  have hi := (hB.operands_l I hc hs).1
  have hiω := hω.transitive hZF b hb i hi
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 u huω
  have bt : M.MemberSubset b t := fun x hx => (ht x).mpr (Or.inl hx)
  have tu : M.MemberSubset t u := fun x hx => (hu x).mpr (Or.inl hx)
  have uσ : M.MemberSubset u σ := fun x hx => (hσ x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hbi : b ≠ i := fun e => ir i (e ▸ hi)
  have hti : t ≠ i := fun e => ir i (e ▸ bt i hi)
  have hbt : b ≠ t := fun e => ir t (e ▸ ht.predecessor_mem)
  obtain ⟨m, G, T, h⟩ := pe_compile_bound_l hZF hω hF hb hB ht
  obtain ⟨v, hv, hjv⟩ := h.2.1.2.2 j hj
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_function_l I hZF hω h.1 hσω
    (uσ i (tu i (bt i hi))) (uσ b (tu b ht.predecessor_mem)) hσ.predecessor_mem
    (fun e => ir b (e ▸ tu b ht.predecessor_mem)) (fun e => ir i (e ▸ tu i (bt i hi)))
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span v hv)
  obtain ⟨aD, hDa, haD⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hb hD
  have agree p aT (hu : Senv_update_d I aD t p aT) : Senv_agree_d I b a aT := fun k x hk =>
    (hDa.agree_l I (ir b) k x hk).trans (hu.agree_l I (fun hi => ir t (bt t hi)) k x hk)
  have matrix p g aT aF (hp : M.mem p D) (hg : M.mem g X)
      (hT : Senv_update_d I aD t p aT) (hG : Senv_update_d I aT i g aF) :
      Ssat_d I X R E F₂ n₂ r₂ aF ↔ Sfun_d X D g ∧ Ssat_d I X R E G m v aF := by
    have haF := (hE aF).mpr (hG.function_l I (hT.function_l I haD htω (hX D hD p hp)) hiω hg)
    rw [a₂ X R E aF haF, a₁ X R E c aF g D hX hm hE haF
      ((hG.2 i g).mpr (Or.inl ⟨rfl, rfl⟩)) ((hG.2 b D).mpr (Or.inr ⟨hbi,
        (hT.2 b D).mpr (Or.inr ⟨hbt, (hDa.2 b D).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)),
      ← h₁.sat_l I hZF h.1 hv X R E aF]
  have row p g x aT aF f f' (hp : M.mem p D) (hg : Sfun_d X D g) (hx : Rd_entry_d p x g)
      (hT : Senv_update_d I aD t p aT) (hG : Senv_update_d I aT i g aF)
      (hf : M.mem f E) (he : Pe_assign_d I b D X a f p) (hff : Senv_update_d I f i x f') :
      Ssat_d I X R E F n j f' ↔ Ssat_d I X R E G m v aF :=
    h.2.2 c X R D E (sc_pe_context_l hZF hω hX hm theory hD hE) j v hjv p aF f' hp ((hE aF).mpr (hG.function_l I
      (hT.function_l I haD htω (hX D hD p hp)) hiω hg.1))
      ((hE f').mpr (hff.function_l I ((hE f).mp hf) hiω ((hg.function_l hX).bound_l hx).2))
      ((hG.2 b D).mpr (Or.inr ⟨hbi, (hT.2 b D).mpr
        (Or.inr ⟨hbt, (hDa.2 b D).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩))
      ((hG.2 t p).mpr (Or.inr ⟨hti, (hT.2 t p).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
      ((he.congr_left_l I (agree p aT hT)).update_l I hg hx hG hff)
  obtain ⟨B, C, hBX, hCX, hBC, select⟩ := theory.uniformization E F₂ n₂ r₂ t i aD A hE h₂.program
    h₂.root htω hiω hti ((hE aD).mpr haD) hA (fun p hp => by
      obtain ⟨f, hf, he, hsat⟩ := htot p hp
      obtain ⟨x, f', hx, hff, hsat⟩ := (ssat_exists_l I hZF hF hV hc hs hf).mp hsat
      obtain ⟨g, L, hg, hL, hfL, hcst⟩ := sc_constant_l hZF hω hX hm theory hD hx
      obtain ⟨aT, hT, haT⟩ := senv_update_exists_l I hZF haD htω (hX A hA p hp)
      obtain ⟨aF, hG, _⟩ := senv_update_exists_l I hZF haT hiω hg
      have hfun : Sfun_d X D g := ⟨hg, L, hL, hfL⟩
      exact ⟨g, hg, aT, aF, hT, hG, (matrix p g aT aF (hAD p hp) hg hT hG).mpr
        ⟨hfun, (row p g x aT aF f f' (hAD p hp) hfun ((hcst p x).mpr ⟨hAD p hp, rfl⟩) hT hG hf he hff).mp hsat⟩⟩)
  have chosen p g (hpg : Rd_entry_d p g B) : Sfun_d X D g := by
    obtain ⟨aT, aF, hT, hG, hs⟩ := select p g hpg
    exact ((matrix p g aT aF (hAD p (hBC.bound_l hpg).1) (hX C hCX g (hBC.bound_l hpg).2) hT hG).mp hs).1
  obtain ⟨g, hg, diag⟩ := sc_diagonal_l hZF hω hX hm theory hD hA hBX hCX hAD hBC chosen
  obtain ⟨a', ha', _⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hiω hg.1
  refine ⟨g, a', hg, ha', fun p hp => ?_⟩
  obtain ⟨f, hf, he, _⟩ := htot p hp
  obtain ⟨g', _, hpg⟩ := hBC.2.1 p hp
  obtain ⟨aT, aF, hT, hG, hs⟩ := select p g' hpg
  have hfun := chosen p g' hpg
  obtain ⟨x, hx, hpx⟩ := (hfun.function_l hX).2.1 p (hAD p hp)
  obtain ⟨f', hff, hf'⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hiω hx
  exact ⟨f', (hE f').mpr hf', he.update_l I hg ((diag p g' x hpg).mpr hpx) ha' hff,
    (row p g' x aT aF f f' (hAD p hp) hfun hpx hT hG hf he hff).mpr
      ((matrix p g' aT aF (hAD p hp) hfun.1 hT hG).mp hs).2⟩

end YesMetaZFC.SetTheory.Internal
