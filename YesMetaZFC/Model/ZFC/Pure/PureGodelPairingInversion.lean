import YesMetaZFC.Model.ZFC.Pure.PureArithmeticOrder

/-! # Gödel 配对在任意内部自然数上的单射性

两分支同处一个平方区间，区间互不重叠；确定区间后由加法消去恢复坐标。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureGodelPairingInversion
open PureModel PureNaturalInduction PureArithmeticStage PureArithmeticSpecifications
open PureArithmeticBounds PureArithmeticOrder
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

def Band (hℳ : Theory.Models ℳ theory) (shell output : Carrier ℳ) : Prop :=
  Le (mul hℳ shell shell) output ∧
    membership ℳ output (mul hℳ (succ hℳ shell) (succ hℳ shell))

theorem first_band (hℳ : Theory.Models ℳ theory) {a b : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hLess : membership ℳ a b) : Band hℳ b (PureGodelPairing.firstBranch hℳ a b) := by
  change Band hℳ b (add hℳ (power hℳ b (PureGodelPairing.two hℳ)) a)
  rw [square_value hℳ hb]
  have hs := arithmetic_closed hℳ .multiplication hb hb
  have hsb := arithmetic_closed hℳ .addition hs hb
  refine ⟨add_left hℳ hs ha, ?_⟩
  rw [square_succ hℳ hb]
  apply (le_iff_succ hℳ _ _).mp
  exact Or.inr (lt_le hℳ (arithmetic_closed hℳ .addition hsb hb)
    (add_lt hℳ hs ha hb hLess) (add_left hℳ hsb hb))

theorem second_band (hℳ : Theory.Models ℳ theory) {a b : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hLess : Le b a) : Band hℳ a (PureGodelPairing.secondBranch hℳ a b) := by
  change Band hℳ a (add hℳ (add hℳ (power hℳ a (PureGodelPairing.two hℳ)) a) b)
  rw [square_value hℳ ha]
  have hs := arithmetic_closed hℳ .multiplication ha ha
  have hsa := arithmetic_closed hℳ .addition hs ha
  refine ⟨le_trans hℳ (arithmetic_closed hℳ .addition hsa hb)
    (add_left hℳ hs ha) (add_left hℳ hsa hb), ?_⟩
  rw [square_succ hℳ ha]
  exact (le_iff_succ hℳ _ _).mp (add_le hℳ hsa hb ha hLess)

theorem band_unique (hℳ : Theory.Models ℳ theory) {a b output : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hOutput : membership ℳ output (omega hℳ))
    (hFirst : Band hℳ a output) (hSecond : Band hℳ b output) : a = b := by
  have hImpossible {left right : Carrier ℳ}
      (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
      (hLT : membership ℳ left right) (hL : Band hℳ left output) (hR : Band hℳ right output) : False := by
    have hSucc : Le (succ hℳ left) right := (le_iff_succ hℳ _ _).mpr
      (successor_mem_successor hℳ hRight hLT)
    have hSquares := square_le hℳ (succ_mem hℳ hLeft) hRight hSucc
    exact lt_irrefl hℳ hOutput (lt_le hℳ hOutput hL.2 (le_trans hℳ hOutput hSquares hR.1))
  rcases PureGodelPairing.compare hℳ ha hb with h | h | h
  · exact False.elim (hImpossible ha hb h hFirst hSecond)
  · exact h.symm
  · exact False.elim (hImpossible hb ha h hSecond hFirst)

theorem branches_ne (hℳ : Theory.Models ℳ theory) {a b c : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hc : membership ℳ c (omega hℳ)) (hLess : membership ℳ a b) :
    PureGodelPairing.firstBranch hℳ a b ≠ PureGodelPairing.secondBranch hℳ b c := by
  intro h
  have hs := arithmetic_closed hℳ .exponentiation hb (succ_mem hℳ (succ_mem hℳ (zero_mem hℳ)))
  have hsb := arithmetic_closed hℳ .addition hs hb
  have hOut := arithmetic_closed hℳ .addition hsb hc
  have hStrict := lt_le hℳ hOut (add_lt hℳ hs ha hb hLess) (add_left hℳ hsb hc)
  change membership ℳ (PureGodelPairing.firstBranch hℳ a b) (PureGodelPairing.secondBranch hℳ b c) at hStrict
  rw [h] at hStrict
  exact lt_irrefl hℳ hOut hStrict

/-- 同一输出的两个自然数配对图见证具有相同坐标。 -/
theorem coordinates_unique (hℳ : Theory.Models ℳ theory) {a b c d output : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hc : membership ℳ c (omega hℳ)) (hd : membership ℳ d (omega hℳ))
    (hFirst : PureGodelPairing.graph.satisfies (templateEnv (.cons output (.cons a (.cons b .nil)))))
    (hSecond : PureGodelPairing.graph.satisfies (templateEnv (.cons output (.cons c (.cons d .nil))))) :
    a = c ∧ b = d := by
  have hF := (PureGodelPairing.specification_correct hℳ a b output).mp
    ((PureGodelPairing.agrees hℳ ha hb output).mp hFirst)
  have hS := (PureGodelPairing.specification_correct hℳ c d output).mp
    ((PureGodelPairing.agrees hℳ hc hd output).mp hSecond)
  rcases PureGodelPairing.compare hℳ ha hb with hAB | hBA
  · have hBand := (hF.2.1 hAB).symm ▸ first_band hℳ ha hb hAB
    rcases PureGodelPairing.compare hℳ hc hd with hCD | hDC
    · have hBD := band_unique hℳ hb hd hF.1 hBand ((hS.2.1 hCD).symm ▸ first_band hℳ hc hd hCD)
      subst d
      refine ⟨?_, rfl⟩
      exact add_cancel hℳ (arithmetic_closed hℳ .exponentiation hb
        (succ_mem hℳ (succ_mem hℳ (zero_mem hℳ)))) ha hc
        ((hF.2.1 hAB).symm.trans (hS.2.1 hCD))
    · have hBC := band_unique hℳ hb hc hF.1 hBand ((hS.2.2 hDC).symm ▸ second_band hℳ hc hd hDC)
      subst c
      exact False.elim (branches_ne hℳ ha hb hd hAB ((hF.2.1 hAB).symm.trans (hS.2.2 hDC)))
  · have hBand := (hF.2.2 hBA).symm ▸ second_band hℳ ha hb hBA
    rcases PureGodelPairing.compare hℳ hc hd with hCD | hDC
    · have hAD := band_unique hℳ ha hd hF.1 hBand ((hS.2.1 hCD).symm ▸ first_band hℳ hc hd hCD)
      subst d
      exact False.elim (branches_ne hℳ hc ha hb hCD ((hS.2.1 hCD).symm.trans (hF.2.2 hBA)))
    · have hAC := band_unique hℳ ha hc hF.1 hBand ((hS.2.2 hDC).symm ▸ second_band hℳ hc hd hDC)
      subst c
      refine ⟨rfl, ?_⟩
      exact add_cancel hℳ (arithmetic_closed hℳ .addition
        (arithmetic_closed hℳ .exponentiation ha (succ_mem hℳ (succ_mem hℳ (zero_mem hℳ)))) ha)
        hb hd ((hF.2.2 hBA).symm.trans (hS.2.2 hDC))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureGodelPairingInversion
