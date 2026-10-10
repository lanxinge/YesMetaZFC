import YesMetaZFC.Model.SetTheory.Internal.PointwiseAssignment
import YesMetaZFC.Model.SetTheory.Internal.PointwiseContext

/-! # 逐点解释的内部行性质与翻译状态

b 同时界住原程序坐标并存放定义域参数，t 存放求值点。翻译状态中的实际
函数图把每条旧指令指向新程序的一行；全部语义条件都有可分离的原公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pe_row_d (b t D X R E F n m G r u : M.Domain) : Prop := ∀ p a f,
  M.mem p D → M.mem a E → M.mem f E → M.PairMember I b D a → M.PairMember I t p a →
    Pe_assign_d I b D X a f p → (Ssat_d I X R E F n r f ↔ Ssat_d I X R E G m u a)

def pe_row_m {d} (b t D X R E F n m G r u : Term d) : Formula 1 d := Formula.forallMem D
  (Formula.forallMem E.weaken (Formula.forallMem E.weaken.weaken
    (.imp (Formula.orderedPairMem 𝒞 b.weaken.weaken.weaken D.weaken.weaken.weaken (.bound 1))
      (.imp (Formula.orderedPairMem 𝒞 t.weaken.weaken.weaken (.bound 2) (.bound 1))
        (.imp (pe_assign_m (𝒞 := 𝒞) b.weaken.weaken.weaken D.weaken.weaken.weaken X.weaken.weaken.weaken
          (.bound 1) .newest (.bound 2))
          (.iff (ssat_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken E.weaken.weaken.weaken
            F.weaken.weaken.weaken n.weaken.weaken.weaken r.weaken.weaken.weaken .newest)
            (ssat_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken E.weaken.weaken.weaken
              G.weaken.weaken.weaken m.weaken.weaken.weaken u.weaken.weaken.weaken (.bound 1))))))))
derive_free_closed pe_row_m

theorem pe_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b t D X R E F n m G r u : Term d) :
    Formula.satisfies ρ (pe_row_m (𝒞 := 𝒞) b t D X R E F n m G r u) ↔
      Pe_row_d I (b.eval ρ) (t.eval ρ) (D.eval ρ) (X.eval ρ) (R.eval ρ) (E.eval ρ)
        (F.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (r.eval ρ) (u.eval ρ) := by
  simp only [pe_row_m, Pe_row_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, pe_assign_sat_l I hE, Formula.satisfies_iff_iff,
    ssat_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h p a f hp ha hf => h p hp a ha f hf, fun h p hp a ha f hf => h p a f hp ha hf⟩

def Pe_state_d (ω b t F n k m G T : M.Domain) : Prop := Sfm_d I ω m G ∧
  M.IsSetFunctionFromTo I T k m ∧ ∀ c X R D E, Pe_context_d I ω c X R D E →
    ∀ r u, M.PairMember I r u T → Pe_row_d I b t D X R E F n m G r u

def pe_state_m {d} (ω b t F n k m G T : Term d) : Formula 1 d :=
  let w (x : Term d) := x.weaken.weaken.weaken.weaken.weaken
  .conj (sfm_m (𝒞 := 𝒞) ω m G) (.conj (Formula.isFunctionFromTo 𝒞 T k m)
    (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
      (pe_context_m (𝒞 := 𝒞) (w ω) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
      (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (w T).weaken.weaken)
        (pe_row_m (𝒞 := 𝒞) (w b).weaken.weaken (w t).weaken.weaken (.bound 3) (.bound 5) (.bound 4)
          (.bound 2) (w F).weaken.weaken (w n).weaken.weaken (w m).weaken.weaken (w G).weaken.weaken
          (.bound 1) .newest)))))))))))
derive_free_closed pe_state_m

theorem pe_state_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b t F n k m G T : Term d) :
    Formula.satisfies ρ (pe_state_m (𝒞 := 𝒞) ω b t F n k m G T) ↔
      Pe_state_d I (ω.eval ρ) (b.eval ρ) (t.eval ρ) (F.eval ρ) (n.eval ρ)
        (k.eval ρ) (m.eval ρ) (G.eval ρ) (T.eval ρ) := by
  simp only [pe_state_m, Pe_state_d, Formula.satisfies_conj_iff, sfm_sat_l I hE,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, pe_context_sat_l I hE,
    pe_row_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem Pe_row_d.extend_l (hZF : M.Models ZF) {ω b t D X R E F n m G r u v J z}
    (h : Pe_row_d I b t D X R E F n m G r u) (hG : Sfm_d I ω m G)
    (hg : Sbuild_d I ω m G v J z) (hu : M.mem u m) : Pe_row_d I b t D X R E F n v J r u :=
  fun p a f hp ha hf hD ht he => (h p a f hp ha hf hD ht he).trans (hg.sat_l I hZF hG hu X R E a)

theorem pe_state_append_l (hZF : M.Models ZF) {ω b t F n k m G T l v J z}
    (hω : M.IsOmega ω) (hk : M.mem k ω) (hl : M.SuccessorOf l k) (h : Pe_state_d I ω b t F n k m G T)
    (hg : Sbuild_d I ω m G v J z) (hz : ∀ c X R D E, Pe_context_d I ω c X R D E → Pe_row_d I b t D X R E F n v J k z) :
    ∃ U, Pe_state_d I ω b t F n l v J U := by
  have hko := hω.members_areOrdinals hZF k hk
  have seq : M.IsSequenceOfLength I T k := ⟨hko, h.2.1.1, h.2.1.2.1⟩
  obtain ⟨U, hU, he⟩ := seq.exists_append (ZF.modelsKP hZF) I (KP.successor_isOrdinal (ZF.modelsKP hZF) hko hl) hl (value := z)
  refine ⟨U, hg.program, ⟨hU.2.1, hU.2.2, fun i hi => ?_⟩, fun c X R D E context r u hu => ?_⟩
  · rcases (hl i).mp hi with hi | hi
    · obtain ⟨u, hu, hiu⟩ := h.2.1.2.2 i hi
      exact ⟨u, hg.span u hu, (he i u).mpr (Or.inl hiu)⟩
    · have eq := hZF.1.eq_of_same_members i k hi
      exact ⟨z, hg.root, (he i z).mpr (Or.inr ⟨eq, rfl⟩)⟩
  · rcases (he r u).mp hu with hu | ⟨rfl, rfl⟩
    · exact (h.2.2 c X R D E context r u hu).extend_l I hZF h.1 hg (h.2.1.output_mem_of_pairMember hu)
    · exact hz c X R D E context

end YesMetaZFC.SetTheory.Internal
