import YesMetaZFC.SetTheory.FlatPairing.Sequence
import YesMetaZFC.Model.SetTheory.Internal.Theory

/-! # 平坦前缀的精确反解

同长度前缀编码相等，当且仅当两份赋值在该长度内逐点相等。
证明一次内部归纳同时给出唯一性与单射性，供满足关系的量词步直接使用。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Fs_trace_d.prefix_l (hZF : M.Models ZF) {ω X f g H G n p q : M.Domain} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo I g ω X)
    (h : Fs_trace_d I ω X f H) (k : Fs_trace_d I ω X g G) (hn : M.mem n ω)
    (hp : M.PairMember I n p H) (hq : M.PairMember I n q G) :
    p = q ↔ Senv_agree_d I n f g := by
  let ρ : Env M 4 := ⟨Fin.cases G (Fin.cases H (Fin.cases g (fun _ => f))), fun _ => f⟩
  let φ : UnarySchema 4 := { body := .forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4))
      (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
        (.iff (Formula.extensionalEq (.bound 1) .newest)
          (senv_agree_m (𝒞 := 𝒞) (.bound 2) (.bound 6) (.bound 5)))))) }
  have sat i : φ.denote ρ i ↔ ∀ p q, M.PairMember I i p H → M.PairMember I i q G →
      (p = q ↔ Senv_agree_d I i f g) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_iff_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, senv_agree_sat_l I]; rfl
  have all : ∀ i, M.mem i ω → ∀ p q, M.PairMember I i p H → M.PairMember I i q G →
      (p = q ↔ Senv_agree_d I i f g) := by
    apply hω.induction
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨C, fun i => (hC i).trans (and_congr_right fun _ => sat i)⟩
    · intro z hz p q hp hq
      exact ⟨fun _ i _ hi => (hz i hi).elim, fun _ =>
        (h.1.1.2 z p z hp (h.2.1 z hz)).trans (k.1.1.2 z z q (k.2.1 z hz) hq)⟩
    · intro i hi ih j succ p q hp hq
      obtain ⟨a, _, ha⟩ := h.1.2.2 i hi
      obtain ⟨b, _, hb⟩ := k.1.2.2 i hi
      obtain ⟨x, _, hx⟩ := hf.2.2 i hi
      obtain ⟨y, _, hy⟩ := hg.2.2 i hi
      have cp := h.2.2 i j a p x succ ha hp hx
      have cq := k.2.2 i j b q y succ hb hq hy
      constructor
      · intro eq
        obtain ⟨ab, xy⟩ := I.injective cp (eq.symm ▸ cq)
        have old := (ih a b ha hb).mp ab
        intro t z ht
        rcases (succ t).mp ht with ht | ht
        · exact old t z ht
        · have ti := hZF.1.eq_of_same_members t i ht
          subst t
          exact ⟨fun hz => hf.1.2 i z x hz hx ▸ xy.symm ▸ hy,
            fun hz => hg.1.2 i z y hz hy ▸ xy ▸ hx⟩
      · intro agree
        have ab := (ih a b ha hb).mpr (fun t z ht => agree t z ((succ t).mpr (Or.inl ht)))
        have xy := hg.1.2 i x y ((agree i x succ.predecessor_mem).mp hx) hy
        exact I.unique cp (ab.symm ▸ xy.symm ▸ cq)
  exact all n hn p q hp hq

def Fs_code_d (ω X f n p : M.Domain) : Prop :=
  ∃ H, Fs_trace_d I ω X f H ∧ M.PairMember I n p H

/-- 扩大对象域保持同一条编码轨道，编码本身不改变。 -/
theorem Fs_code_d.mono_l {ω A B f n p : M.Domain} (h : Fs_code_d I ω A f n p)
    (sub : M.MemberSubset A B) : Fs_code_d I ω B f n p := by
  obtain ⟨H, trace, hp⟩ := h
  exact ⟨H, ⟨⟨trace.1.1, trace.1.2.1, fun i hi =>
    (trace.1.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩, trace.2⟩, hp⟩

def fs_code_m {d} (ω X f n p : Term d) : Formula 1 d := .existsE (.conj
  (fs_trace_m (𝒞 := 𝒞) ω.weaken X.weaken f.weaken .newest)
  (Formula.orderedPairMem 𝒞 n.weaken p.weaken .newest))
derive_free_closed fs_code_m

theorem fs_code_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X f n p : Term d) :
    Formula.satisfies ρ (fs_code_m (𝒞 := 𝒞) ω X f n p) ↔
      Fs_code_d I (ω.eval ρ) (X.eval ρ) (f.eval ρ) (n.eval ρ) (p.eval ρ) := by
  simp only [fs_code_m, Fs_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fs_trace_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem Fs_code_d.prefix_l (hZF : M.Models ZF) {ω X f g n p q : M.Domain} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo I g ω X)
    (h : Fs_code_d I ω X f n p) (k : Fs_code_d I ω X g n q) : p = q ↔ Senv_agree_d I n f g := by
  obtain ⟨H, hH, hp⟩ := h
  obtain ⟨G, hG, hq⟩ := k
  exact hH.prefix_l I hZF hω hf hg hG (hH.1.input_mem_of_pairMember hp) hp hq

theorem Fs_code_d.bound_l {ω X f n p : M.Domain} (h : Fs_code_d I ω X f n p) : M.mem n ω ∧ M.mem p X :=
  h.elim fun _ h => ⟨h.1.1.input_mem_of_pairMember h.2, h.1.1.output_mem_of_pairMember h.2⟩

theorem Fs_code_d.transport_l (hZF : M.Models ZF) {ω X f g G n p : M.Domain} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo I g ω X)
    (trace : Fs_trace_d I ω X g G) (h : Fs_code_d I ω X f n p) (agree : Senv_agree_d I n f g) :
    Fs_code_d I ω X g n p := by
  obtain ⟨q, _, hq⟩ := trace.1.2.2 n (h.bound_l I).1
  have code : Fs_code_d I ω X g n q := ⟨G, trace, hq⟩
  exact ((h.prefix_l I hZF hω hf hg code).mpr agree).symm ▸ code

end YesMetaZFC.SetTheory
