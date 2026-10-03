import YesMetaZFC.SetTheory.Collapse.RelationEvaluation

/-! # 合并全部相容部分解，得到实际良基递归函数

部分图由 X×Y 的幂集承载。收集全部部分解再取并，无需选择前驱解。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable (hZF : M.Models ZF) {n} {φ : BinarySchema (n+1)} {ρ : Env M n} {X R Y : M.Domain}
variable (ht : ∀ a G, M.mem a X → M.IsSetFunction I G →
  (∀ b, M.mem b X → Rd_entry_d b a R → ∃ d, M.mem d Y ∧ M.PairMember I b d G) →
    ∃ c, M.mem c Y ∧ φ.denote (ρ.push G) a c)
variable (hu : ∀ a G H c d, M.mem a X → M.IsSetFunction I G → M.IsSetFunction I H →
  (∀ b v, M.mem b X → Rd_entry_d b a R → (M.PairMember I b v G ↔ M.PairMember I b v H)) →
    φ.denote (ρ.push G) a c → φ.denote (ρ.push H) a d → c = d)
include hZF ht hu

theorem wfr_adjoin_l {G a c} (hG : Wfr_d I φ ρ X R Y G) (ha : M.mem a X) (hc : M.mem c Y)
    (hna : ¬ ∃ d, M.PairMember I a d G)
    (ready : ∀ b, M.mem b X → Rd_entry_d b a R → ∃ d, M.mem d Y ∧ M.PairMember I b d G)
    (hop : φ.denote (ρ.push G) a c) : ∃ F, Wfr_d I φ ρ X R Y F ∧ M.PairMember I a c F := by
  obtain ⟨p, hp⟩ := I.total a c
  obtain ⟨F, hf⟩ := KP.exists_insert (ZF.modelsKP hZF) G p
  have pair b d : M.PairMember I b d F ↔ M.PairMember I b d G ∨ (b = a ∧ d = c) := by
    constructor
    · rintro ⟨q, hq, hqF⟩
      exact ((hf q).mp hqF).elim (fun h => Or.inl ⟨q, hq, h⟩) (fun e => Or.inr (I.injective (e ▸ hq) hp))
    · rintro (⟨q, hq, hqG⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, hq, (hf q).mpr (Or.inl hqG)⟩
      · exact ⟨p, hp, (hf p).mpr (Or.inr rfl)⟩
  have fn : M.IsSetFunction I F := by
    refine ⟨fun q hq => ((hf q).mp hq).elim (hG.1.1 q) (fun e => ⟨a, c, e.symm ▸ hp⟩), ?_⟩
    intro b d e hd he
    rcases (pair b d).mp hd with hd | hd <;> rcases (pair b e).mp he with he | he
    · exact hG.1.2 b d e hd he
    · exact (hna ⟨d, he.1 ▸ hd⟩).elim
    · exact (hna ⟨e, hd.1 ▸ he⟩).elim
    · exact hd.2.trans he.2.symm
  have transfer {b d} (hb : M.mem b X)
      (hr : ∀ s, M.mem s X → Rd_entry_d s b R → ∃ v, M.mem v Y ∧ M.PairMember I s v G)
      (hv : φ.denote (ρ.push G) b d) : φ.denote (ρ.push F) b d := by
    obtain ⟨e, _, he⟩ := ht b F hb fn (fun s hs hsb => (hr s hs hsb).imp fun v hv => ⟨hv.1, (pair s v).mpr (Or.inl hv.2)⟩)
    have eqn s v (hs : M.mem s X) (hsb : Rd_entry_d s b R) : M.PairMember I s v G ↔ M.PairMember I s v F := by
      refine ⟨fun h => (pair s v).mpr (Or.inl h), fun hv => ?_⟩
      obtain ⟨w, _, hw⟩ := hr s hs hsb
      exact fn.2 s w v ((pair s w).mpr (Or.inl hw)) hv ▸ hw
    exact (hu b G F d e hb hG.1 fn eqn hv he).symm ▸ he
  refine ⟨F, ⟨fn, fun b d hbd => ?_⟩, (pair a c).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  have ready_old {b d} (hbd : M.PairMember I b d G) s (hs : M.mem s X) (hsb : Rd_entry_d s b R) :
      ∃ v, M.mem v Y ∧ M.PairMember I s v G := by
    obtain ⟨v, hv⟩ := (hG.2 b d hbd).2.2.1 s hs hsb
    exact ⟨v, (hG.2 s v hv).2.1, hv⟩
  rcases (pair b d).mp hbd with hbd | ⟨rfl, rfl⟩
  · have h := hG.2 b d hbd
    exact ⟨h.1, h.2.1, fun s hs hsb => (ready_old hbd s hs hsb).imp fun v hv => (pair s v).mpr (Or.inl hv.2),
      transfer h.1 (ready_old hbd) h.2.2.2⟩
  · exact ⟨ha, hc, fun s hs hsb => (ready s hs hsb).imp fun v hv => (pair s v).mpr (Or.inl hv.2), transfer ha ready hop⟩

/-- 有界值域良基递归的实际总图；算子的具体实例由调用者的原公式给出。 -/
theorem wf_bounded_recursion_l (hw : Wf_rel_d X R) :
    ∃ G, M.IsSetFunctionFromTo I G X Y ∧ ∀ a c, M.PairMember I a c G → φ.denote (ρ.push G) a c := by
  classical
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I X Y
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  let η := ((ρ.push X).push R).push Y
  let ψ : UnarySchema (n+3) := {
    body := wfr_m (𝒞 := 𝒞) φ (Definitional.TermVector.boundParameters n 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp H : ψ.denote η H ↔ Wfr_d I φ ρ X R Y H := by
    simp only [ψ, η, UnarySchema.denote, wfr_sat_l I hZF.1, Definitional.TermVector.evalEnv_boundParameters_four]; rfl
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF ψ η Q
  have hC H : M.mem H C ↔ Wfr_d I φ ρ X R Y H := ((hC' H).trans
    (and_congr_right fun _ => hp H)).trans ⟨And.right, fun h => ⟨(hQ H).mpr (fun p hp => by
      obtain ⟨a, c, hac⟩ := h.1.1 p hp
      have hh := h.2 a c ⟨p, hac, hp⟩
      exact (hP p).mpr ⟨a, hh.1, c, hh.2.1, hac⟩), h⟩⟩
  obtain ⟨G, hg⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have pair a c : M.PairMember I a c G ↔ ∃ H, Wfr_d I φ ρ X R Y H ∧ M.PairMember I a c H := by
    constructor
    · rintro ⟨p, hp, hpg⟩
      obtain ⟨H, hHC, hpH⟩ := (hg p).mp hpg
      exact ⟨H, (hC H).mp hHC, p, hp, hpH⟩
    · rintro ⟨H, hH, p, hp, hpH⟩
      exact ⟨p, hp, (hg p).mpr ⟨H, (hC H).mpr hH, hpH⟩⟩
  have fn : M.IsSetFunction I G := by
    refine ⟨fun p hp => ((hg p).mp hp).elim fun H h => ((hC H).mp h.1).1.1 p h.2, ?_⟩
    intro a c d hc hd
    obtain ⟨H, hH, hc⟩ := (pair a c).mp hc
    obtain ⟨F, hF, hd⟩ := (pair a d).mp hd
    exact wfr_agree_l I hZF hw hu hH hF a c d hc hd
  have part : Wfr_d I φ ρ X R Y G := by
    refine ⟨fn, fun a c hac => ?_⟩
    obtain ⟨H, hH, hac⟩ := (pair a c).mp hac
    have h := hH.2 a c hac
    have ready b (hb : M.mem b X) (hba : Rd_entry_d b a R) : ∃ d, M.mem d Y ∧ M.PairMember I b d G := by
      obtain ⟨d, hd⟩ := h.2.2.1 b hb hba
      exact ⟨d, (hH.2 b d hd).2.1, (pair b d).mpr ⟨H, hH, hd⟩⟩
    obtain ⟨d, _, hd⟩ := ht a G h.1 fn ready
    have eqn b v (hb : M.mem b X) (hba : Rd_entry_d b a R) : M.PairMember I b v H ↔ M.PairMember I b v G := by
      refine ⟨fun hv => (pair b v).mpr ⟨H, hH, hv⟩, fun hv => ?_⟩
      obtain ⟨w, hw⟩ := h.2.2.1 b hb hba
      exact fn.2 b w v ((pair b w).mpr ⟨H, hH, hw⟩) hv ▸ hw
    exact ⟨h.1, h.2.1, fun b hb hba => (ready b hb hba).imp fun _ hv => hv.2,
      (hu a H G c d h.1 hH.1 fn eqn h.2.2.2 hd).symm ▸ hd⟩
  have total : ∀ a, M.mem a X → ∃ c, M.PairMember I a c G := by
    let θ : UnarySchema 1 := { body := .existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2)) }
    let δ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
    have hp a : θ.denote δ a ↔ ∃ c, M.PairMember I a c G := by
      simp only [θ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
    have all := wf_rel_ind_l hZF hw θ δ (fun a ha ih => (hp a).mpr (by
      by_cases hn : ∃ c, M.PairMember I a c G
      · exact hn
      · have ready b (hb : M.mem b X) (hba : Rd_entry_d b a R) : ∃ c, M.mem c Y ∧ M.PairMember I b c G := by
          obtain ⟨c, hc⟩ := (hp b).mp (ih b hb hba)
          exact ⟨c, (part.2 b c hc).2.1, hc⟩
        obtain ⟨c, hcY, hc⟩ := ht a G ha fn ready
        obtain ⟨F, hF, hac⟩ := wfr_adjoin_l I hZF ht hu part ha hcY hn ready hc
        exact ⟨c, (pair a c).mpr ⟨F, hF, hac⟩⟩))
    exact fun a ha => (hp a).mp (all a ha)
  exact ⟨G, ⟨fn, fun a => ⟨total a, fun ⟨c, hc⟩ => (part.2 a c hc).1⟩,
    fun a ha => (total a ha).imp fun c hc => ⟨(part.2 a c hc).2.1, hc⟩⟩,
    fun a c hc => (part.2 a c hc).2.2.2⟩

end YesMetaZFC.SetTheory
