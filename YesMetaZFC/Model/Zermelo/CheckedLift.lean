import YesMetaZFC.Model.Zermelo.Capture
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTreeCheck

/-! # 原 ZF 检查器的标准数码捕获与升层

只复用 Rosser 工程的计算检查核。原 ZF 公理保留全部模式；现有检查器签名
把子集作为原子，故同时带上该原子的原定义。没有任何 Models ZF 输入。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open SetTheory SetTheory.Definitional
open ProofT ProofT.ZFC QuineEncoding
universe u
attribute [local implicit_reducible] SetTheory.signature

private def cp_ax_ok : ZFCAxiomCertificate → Bool
  | .choice => false
  | _ => true

/-- 原 Project ZF 在现有检查器签名中的逐句像。 -/
private def cp_source : Nonlogical.BasicSetTheory.SetTheory :=
  fun φ => ∃ s, SetTheory.ZF s ∧ project_sentence s = φ

private def cp_source_axioms : AxiomPresentation cp_source where
  Certificate := {c : ZFCAxiomCertificate // cp_ax_ok c = true}
  sentence c := project_sentence c.val.sentence
  sound := by
    rintro ⟨c, h⟩
    refine ⟨c.sentence, ?_, rfl⟩
    cases c with
    | extensionality => exact .extensionality
    | emptySet => exact .emptySet
    | pairing => exact .pairing
    | union => exact .union
    | powerSet => exact .powerSet
    | infinity => exact .infinity
    | foundation => exact .foundation
    | choice => cases h
    | separation φ => exact .separation φ
    | collection φ => exact .collection φ
  complete := by
    rintro φ ⟨s, h, rfl⟩
    cases h with
    | extensionality => exact ⟨⟨.extensionality, rfl⟩, rfl⟩
    | emptySet => exact ⟨⟨.emptySet, rfl⟩, rfl⟩
    | pairing => exact ⟨⟨.pairing, rfl⟩, rfl⟩
    | union => exact ⟨⟨.union, rfl⟩, rfl⟩
    | powerSet => exact ⟨⟨.powerSet, rfl⟩, rfl⟩
    | infinity => exact ⟨⟨.infinity, rfl⟩, rfl⟩
    | foundation => exact ⟨⟨.foundation, rfl⟩, rfl⟩
    | separation φ => exact ⟨⟨.separation φ, rfl⟩, rfl⟩
    | collection φ => exact ⟨⟨.collection φ, rfl⟩, rfl⟩

private def cp_source_decoder : AxiomDecoder cp_source_axioms := fun t => do
  let c ← zfc_base_axiom_decode t
  if h : cp_ax_ok c = true then some ⟨c, h⟩ else none

private def cp_source_codec : AxiomCodec cp_source_decoder where
  encode c := zfc_base_axiom_encode c.val
  roundtrip c := by
    rcases c with ⟨c, h⟩
    dsimp only [cp_source_decoder]
    rw [zfc_base_axiom_roundtrip]
    simp [h]

/-- 子集符号的定义随源公式一起进入检查，不能把它当作未解释的新关系。 -/
def cp_theory : Nonlogical.BasicSetTheory.SetTheory :=
  Theory.insert Nonlogical.BasicSetTheory.subset_definition_axiom cp_source

def cp_axioms : AxiomPresentation cp_theory :=
  AxiomPresentation.insert Nonlogical.BasicSetTheory.subset_definition_axiom cp_source_axioms

def cp_decoder : AxiomDecoder cp_axioms :=
  AxiomDecoder.insert Nonlogical.BasicSetTheory.subset_definition_axiom cp_source_decoder

def cp_codec : AxiomCodec cp_decoder :=
  AxiomCodec.insert Nonlogical.BasicSetTheory.subset_definition_axiom cp_source_codec

def cp_checked (s : Project.Sentence) (p : Nat) : Bool :=
  ProofTreeCode.checked cp_decoder p (project_sentence s)

/-- 捕获全部实际通过检查的标准证明码，不增加任何理论公理。 -/
def cp_proofs (s : Project.Sentence) : V.{u} := cp_set (cp_checked s)

theorem cp_proofs_sound (s : Project.Sentence) (p : Nat) (h : V.nat.{u} p ∈ cp_proofs s) :
    Derives cp_theory [] (project_sentence s) :=
  ProofTreeCode.checked_sound cp_decoder ((cp_set_mem (cp_checked s) p).mp h)

theorem cp_proofs_complete (s : Project.Sentence) (h : Derives cp_theory [] (project_sentence s)) :
    ∃ p, V.nat.{u} p ∈ cp_proofs s := by
  obtain ⟨p, hp⟩ := ProofTreeCode.checked_complete cp_codec h
  exact ⟨p, (cp_set_mem (cp_checked s) p).mpr hp⟩

/-- 高层重新运行同一检查定义，得到旧捕获集的升层像。 -/
theorem cp_proofs_lift (s : Project.Sentence) :
    V.eq (gl_lift (cp_proofs.{u} s)) (cp_proofs s) := cp_set_lift (cp_checked s)

/-- 原模式的一项实际参数由标准证明检查器给出。 -/
def cp_params {n} (s : Project.Sentence) (ρ : Env.{u} (Project.fo_bound_context n) []) :
    Env.{u} (Project.fo_bound_context (n+1)) [] := ρ.pushBound (cp_proofs s)

/-- 高层重新捕获证明集以后，原关系正文的真值仍与低层对应。 -/
theorem cp_matrix_lift {n} (s : Project.Sentence) (φ : Project.BinarySchema (n+1)) (r : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context n) []) (x y : V.{u}) :
    sc_sat (Project.fo_formula φ.body φ.freeClosed) (gl_lift r)
      (((cp_params s (gl_env ρ)).pushBound (gl_lift x)).pushBound (gl_lift y)) ↔
    sc_sat (Project.fo_formula φ.body φ.freeClosed) r
      (((cp_params s ρ).pushBound x).pushBound y) := by
  apply Iff.trans ?_ (gl_abs (Project.fo_formula φ.body φ.freeClosed) r
    (((cp_params s ρ).pushBound x).pushBound y))
  apply sat_congr
  constructor
  · intro t j
    cases j with
    | here => exact V.eq_refl _
    | there j => cases j with
      | here => exact V.eq_refl _
      | there j => cases j with
        | here => exact V.eq_symm (cp_proofs_lift s)
        | there _ => exact V.eq_refl _
  · intro t j
    cases j with
    | here => exact V.eq_refl _
    | there j => nomatch j

/-- 检查集与收集容器都在高层重新构造，结果仍是旧容器的升层像。 -/
theorem cp_collect_rebuild {n} (s : Project.Sentence) (φ : Project.BinarySchema (n+1))
    (r i w : V.{u}) (ρ : Env.{u} (Project.fo_bound_context n) []) (a : V.{u}) :
    V.eq (gl_lift (sc_collect φ r i w (cp_params s ρ) a))
      (sc_collect φ (gl_lift r) (gl_lift i) (gl_lift w) (cp_params s (gl_env ρ)) (gl_lift a)) := by
  apply V.eq_trans (cp_collect_lift φ r i w (cp_params s ρ) a)
  apply cp_collect_congr
  constructor
  · intro t j
    cases j with
    | here => exact cp_proofs_lift s
    | there _ => exact V.eq_refl _
  · intro t j
    nomatch j

/-- info: 'YesMetaZFC.Model.Zermelo.cp_proofs_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cp_proofs_sound
/-- info: 'YesMetaZFC.Model.Zermelo.cp_proofs_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cp_proofs_complete
/-- info: 'YesMetaZFC.Model.Zermelo.cp_matrix_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cp_matrix_lift
/-- info: 'YesMetaZFC.Model.Zermelo.cp_collect_rebuild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cp_collect_rebuild

end YesMetaZFC.Model.Zermelo
