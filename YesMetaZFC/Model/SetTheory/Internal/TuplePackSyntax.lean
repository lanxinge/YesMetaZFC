import YesMetaZFC.Model.SetTheory.Internal.ProgramRecodeSemantics
import YesMetaZFC.Model.SetTheory.Internal.Compiler
import YesMetaZFC.SetTheory.FlatPairing.RankObjects

/-! # 内部变量列的递归打包规格

前缀从空集开始，每次把新坐标平坦配到旧前缀之后。
编译规格对实际秩层与全部赋值统一量化，原 ω 和输出位置由变量槽指定。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Fs_code_d.step_l (hE : Extensional M) {ω X f n l p x : M.Domain}
    (hω : M.IsInductive ω) (hn : M.mem n ω) (hs : M.SuccessorOf l n) (hx : M.PairMember I n x f) :
    Fs_code_d I ω X f l p ↔ ∃ q, Fs_code_d I ω X f n q ∧ I.Codes p q x := by
  obtain ⟨l', hl', hlω⟩ := hω.2 n hn
  have hl := hl'.eq hE hs ▸ hlω
  constructor
  · rintro ⟨H, trace, hp⟩
    obtain ⟨q, _, hq⟩ := trace.1.2.2 n hn
    exact ⟨q, ⟨H, trace, hq⟩, trace.2.2 n l q p x hs hq hp hx⟩
  · rintro ⟨q, ⟨H, trace, hq⟩, code⟩
    obtain ⟨p', _, hp'⟩ := trace.1.2.2 l hl
    exact ⟨H, trace, I.unique (trace.2.2 n l q p' x hs hq hp' hx) code ▸ hp'⟩

theorem Fs_trace_d.zero_code_l (hE : Extensional M) {ω X f H e p : M.Domain}
    (h : Fs_trace_d I ω X f H) (he : ∀ x, ¬ M.mem x e) :
    Fs_code_d I ω X f e p ↔ ∀ x, ¬ M.mem x p := by
  constructor
  · rintro ⟨G, trace, hp⟩
    exact trace.1.1.2 e e p (trace.2.1 e he) hp ▸ he
  · intro hp
    have eq := hE.eq_of_same_members e p (fun x => iff_of_false (he x) (hp x))
    exact ⟨H, h, eq ▸ h.2.1 e he⟩

namespace Internal
variable (Q : kpair_convention_l.Interpretation M) (K : FlatPairing.convention.Interpretation M)

def St_pack_d (ω w b k m G u : M.Domain) : Prop := ∀ μ Y c R E f g p,
  V_d Q μ Y → M.mem ω Y → Smem_d Q c Y R → M.IsFunctionSpace Q E ω Y → M.mem f E →
    M.IsSetFunctionFromTo K g ω Y → Sx_graph_d Q K f g → M.PairMember Q w ω f → M.PairMember Q b p f →
      (Ssat_d Q Y R E G m u f ↔ Fs_code_d K ω Y g k p)

def st_pack_m {d} (ω w b k m G u : Term d) : Formula 1 d := set[d] ⟪∀ μ Y c R E f g p,
  ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜ω⌝ₛ ∈ Y → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, Y) → f ∈ E →
  ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(g, ⌜ω⌝ₛ, Y) →
  ⌜sx_graph_m (𝒞 := kpair_convention_l) (𝒟 := FlatPairing.convention)⌝ₚ(f, g) →
  ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜w⌝ₛ, ⌜ω⌝ₛ, f) →
  ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜b⌝ₛ, p, f) →
    (⌜ssat_m (𝒞 := kpair_convention_l)⌝ₚ(Y, R, E, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, f) ↔
      ⌜fs_code_m (𝒞 := FlatPairing.convention)⌝ₚ(⌜ω⌝ₛ, Y, g, ⌜k⌝ₛ, p))⟫

@[simp] theorem st_pack_closed_l {d} (ω w b k m G u : Term d)
    (hω : ω.freeSupport = []) (hw : w.freeSupport = []) (hb : b.freeSupport = []) (hk : k.freeSupport = [])
    (hm : m.freeSupport = []) (hG : G.freeSupport = []) (hu : u.freeSupport = []) :
    (st_pack_m ω w b k m G u).FreeClosed := by
  simp -implicitDefEqProofs [st_pack_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hω, hw, hb, hk, hm, hG, hu]

theorem st_pack_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω w b k m G u : Term d) :
    Formula.satisfies ρ (st_pack_m ω w b k m G u) ↔
      St_pack_d Q K (ω.eval ρ) (w.eval ρ) (b.eval ρ) (k.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [st_pack_m, St_pack_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    v_sat_l Q hE, Formula.satisfies_mem_iff, smem_sat_l Q, Formula.satisfies_isFunctionSpace_iff Q hE,
    Formula.satisfies_isFunctionFromTo_iff K hE, sx_graph_sat_l Q K, Formula.satisfies_orderedPairMem_iff Q,
    Formula.satisfies_iff_iff, ssat_sat_l Q hE, fs_code_sat_l K hE, Definitional.Term.eval_weaken]; rfl

end Internal
end YesMetaZFC.SetTheory
