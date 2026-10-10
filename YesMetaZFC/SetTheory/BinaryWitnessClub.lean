import YesMetaZFC.SetTheory.FinitaryClub
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd

/-! # 任意二参数原公式的内部见证闭 club

把两个输入作为有限列的末两项，实际选择其存在见证，再对这张有限元运算图
取闭包。整个构造可细化任意已有 club，允许任意固定参数及有序对约定。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bw_wit_d {n} (φ : UnarySchema (n+2)) (ρ : Env M n) (ω F x : M.Domain) : Prop :=
  ∃ s t a b, Fseq_end_d I ω F s b ∧ Fseq_end_d I ω s t a ∧ φ.denote ((ρ.push a).push b) x

def bw_wit_m {n d} (φ : UnarySchema (n+2)) (e : Fin n → Term d) (ω F x : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (fseq_end_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken (.bound 3) .newest)
      (.conj (fseq_end_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1))
        (pred_m φ (Fin.cases .newest (Fin.cases (.bound 1) (fun i => (e i).weaken.weaken.weaken.weaken)))
          x.weaken.weaken.weaken.weaken))))))

@[simp] theorem bw_wit_closed_l {n d} (φ : UnarySchema (n+2)) (e : Fin n → Term d) (ω F x : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hω : ω.freeSupport = []) (hF : F.freeSupport = [])
    (hx : x.freeSupport = []) : (bw_wit_m (𝒞 := 𝒞) φ e ω F x).FreeClosed := by
  have h : ∀ i, (Fin.cases .newest (Fin.cases (.bound 1)
      (fun i => (e i).weaken.weaken.weaken.weaken)) i : Term (d+4)).freeSupport = [] :=
    Fin.cases rfl (Fin.cases rfl (fun i => by simpa using he i))
  simp -implicitDefEqProofs [bw_wit_m, Definitional.Formula.FreeClosed, h, hω, hF, hx]

theorem bw_wit_sat_l (hE : Extensional M) {n d} (φ : UnarySchema (n+2)) (ρ : Env M d)
    (e : Fin n → Term d) (ω F x : Term d) :
    Formula.satisfies ρ (bw_wit_m (𝒞 := 𝒞) φ e ω F x) ↔
      Bw_wit_d I φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (ω.eval ρ) (F.eval ρ) (x.eval ρ) := by
  have h s t a b : (⟨fun i => (Fin.cases .newest (Fin.cases (.bound 1)
      (fun i => (e i).weaken.weaken.weaken.weaken)) i : Term (d+4)).eval ((((ρ.push s).push t).push a).push b),
      ((((ρ.push s).push t).push a).push b).free⟩ : Env M (n+2)) =
      ((⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n).push a).push b := by
    rw [Env.mk.injEq]
    refine ⟨funext (Fin.cases rfl (Fin.cases rfl (fun i => ?_))), rfl⟩
    change (e i).weaken.weaken.weaken.weaken.eval ((((ρ.push s).push t).push a).push b) = (e i).eval ρ
    simp only [Definitional.Term.eval_weaken]
  simp only [bw_wit_m, Bw_wit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE, pred_sat_l M, Definitional.Term.eval_weaken, h]
  rfl

/-- 细化任意内部 club，使每个成员都承接指定二参数公式在环境 X 中的见证。 -/
theorem ZFC.bw_club_l (hZFC : M.Models ZFC) {ω X C} (hω : M.IsOmega ω)
    (hC : Cc_club_d I ω X C) {n} (φ : UnarySchema (n+2)) (ρ : Env M n) :
    ∃ V, Cc_club_d I ω X V ∧ ∀ N, M.mem N V → M.mem N C ∧
      ∀ a b, M.mem a N → M.mem b N → (∃ x, M.mem x X ∧ φ.denote ((ρ.push a).push b) x) →
        ∃ x, M.mem x N ∧ φ.denote ((ρ.push a).push b) x := by
  classical
  have hZF := models_zf_l hZFC
  by_cases hX : ∃ u, M.mem u X
  · obtain ⟨u, hu⟩ := hX
    obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF hω X
    obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I ω S
    let η := ((ρ.push ω).push X).push u
    let ψ : BinarySchema (n+3) := {
      body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest)
        (.disj (bw_wit_m (𝒞 := 𝒞) φ (fun i => .bound ⟨i.val+7, by omega⟩) (.bound 6) .newest (.bound 2))
          (.conj (.neg (.existsE (.conj (.mem .newest (.bound 6))
            (bw_wit_m (𝒞 := 𝒞) φ (fun i => .bound ⟨i.val+8, by omega⟩) (.bound 7) (.bound 1) .newest))))
            (Formula.extensionalEq (.bound 2) (.bound 4)))))) }
    have hψ k x : ψ.denote η k x ↔ ∃ l F, I.Codes k l F ∧
        (Bw_wit_d I φ ρ ω F x ∨ ((¬ ∃ y, M.mem y X ∧ Bw_wit_d I φ ρ ω F y) ∧ x = u)) := by
      simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        I.realizes, Formula.satisfies_disj_iff, bw_wit_sat_l I hZF.1, Formula.satisfies_neg_iff,
        Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
      rfl
    obtain ⟨K, hK, hk⟩ := uniformize_formula_l I hZFC ψ η (X := D) (Y := X) (by
      intro k hk
      obtain ⟨l, _, F, _, hk⟩ := (hD k).mp hk
      by_cases h : ∃ x, M.mem x X ∧ Bw_wit_d I φ ρ ω F x
      · obtain ⟨x, hx, hw⟩ := h
        exact ⟨x, hx, (hψ k x).mpr ⟨l, F, hk, Or.inl hw⟩⟩
      · exact ⟨u, hu, (hψ k u).mpr ⟨l, F, hk, Or.inr ⟨h, rfl⟩⟩⟩)
    obtain ⟨J, hJ⟩ := ZF.exists_identityBijection hZF I ω
    obtain ⟨V, hV, hv⟩ := fc_club_refine_l I hZFC hω hS hD hK ⟨J, hJ.1⟩ hC
    refine ⟨V, hV, fun N hN => ⟨((hv N).mp hN).1, fun a b ha hb hex => ?_⟩⟩
    have hNX := (hC.members N ((hv N).mp hN).1).1
    obtain ⟨o, ho, hoω⟩ := hω.1.1
    have hEmpty : M.IsSetFunctionFromTo I o o N :=
      ⟨(Structure.IsSequenceOfLength.empty I ho).2.1, (Structure.IsSequenceOfLength.empty I ho).2.2,
        fun i hi => (ho i hi).elim⟩
    obtain ⟨m, s, hm, hs, hsa⟩ := ZF.fseq_end_exists_l I hZF hω hoω hEmpty ha
    obtain ⟨v, F, hvω, hF, hFb⟩ := ZF.fseq_end_exists_l I hZF hω hm hs hb
    obtain ⟨k, hko⟩ := I.total o F
    obtain ⟨x, _, hkx⟩ := hK.2.2 k ((hD k).mpr
      ⟨o, hoω, F, (hS F).mpr ⟨v, hvω, hF.mono_target_l I hNX⟩, hko⟩)
    have hxN := ((hv N).mp hN).2 x ⟨v, F, o, k, hvω, hF, hoω, hko, hkx⟩
    obtain ⟨l', F', hk', hx⟩ := (hψ k x).mp (hk k x hkx)
    obtain ⟨rfl, rfl⟩ := I.injective hko hk'
    rcases hx with ⟨s', t', a', b', hFb', hsa', hx⟩ | hx
    · obtain ⟨rfl, rfl⟩ := fseq_end_unique_l I hZF.1 hFb hFb'
      obtain ⟨_, rfl⟩ := fseq_end_unique_l I hZF.1 hsa hsa'
      exact ⟨x, hxN, hx⟩
    · obtain ⟨y, hy, hφ⟩ := hex
      exact (hx.1 ⟨y, hy, s, o, a, b, hFb, hsa, hφ⟩).elim
  · exact ⟨C, hC, fun N hN => ⟨hN, fun a _ ha _ _ => (hX ⟨a, (hC.members N hN).1 a ha⟩).elim⟩⟩

end YesMetaZFC.SetTheory
