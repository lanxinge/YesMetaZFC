import YesMetaZFC.Model.Forcing.Iteration.Proper.Lemma
import YesMetaZFC.Model.Forcing.Proper.Elementary.Countable

/-! # 内部有限阶段的完整区间迭代引理

区间命题由原公式统一表达。沿模型自身的 ω 归纳，以恒等区间为起点，后继使用
实际相邻迭代引理与区间复合；因此结论同样覆盖外部非标准的内部有限阶段。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Row_pil_stage_d (I : kpair_convention_l.Interpretation M) (F G b N β : M.Domain) : Prop :=
  ∀ α B R D V, M.mem α N → M.MemberSubset α β → Entry_d M α B F → Entry_d M α R G →
    Entry_d M β D F → Entry_d M β V G → Row_pil_d I α B R b D V N

def row_pil_stage_m {n} (F G b N β : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 4) N.weaken.weaken.weaken.weaken.weaken)
      (.imp (Formula.subset (.bound 4) β.weaken.weaken.weaken.weaken.weaken)
        (.imp (entry_m (.bound 4) (.bound 3) F.weaken.weaken.weaken.weaken.weaken)
          (.imp (entry_m (.bound 4) (.bound 2) G.weaken.weaken.weaken.weaken.weaken)
            (.imp (entry_m β.weaken.weaken.weaken.weaken.weaken (.bound 1) F.weaken.weaken.weaken.weaken.weaken)
              (.imp (entry_m β.weaken.weaken.weaken.weaken.weaken .newest G.weaken.weaken.weaken.weaken.weaken)
                (row_pil_m (.bound 4) (.bound 3) (.bound 2) b.weaken.weaken.weaken.weaken.weaken
                  (.bound 1) .newest N.weaken.weaken.weaken.weaken.weaken)))))))))))
derive_free_closed row_pil_stage_m

theorem row_pil_stage_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (F G b N β : Term n) : Formula.satisfies ρ (row_pil_stage_m F G b N β) ↔
      Row_pil_stage_d I (F.eval ρ) (G.eval ρ) (b.eval ρ) (N.eval ρ) (β.eval ρ) := by
  simp only [row_pil_stage_m, Row_pil_stage_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, entry_sat_l M hE, row_pil_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

/-- 实际相邻区间统一推出全部内部有限区间；归纳本身只需 ZF。 -/
theorem row_pil_nat_l (hZF : M.Models ZF) {ω χ H c J d N S δ F G b}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H J N S)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d) (hωN : M.mem ω N)
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F G b)
    (hn : ∀ α β B R D V, M.mem α N → M.SuccessorOf β α → Entry_d M α B F → Entry_d M α R G →
      Entry_d M β D F → Entry_d M β V G →
        Row_pil_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N) :
    ∀ β, M.mem β ω → Row_pil_stage_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F G b N β := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hωsub := selem_omega_subset_l I hJ (ZF.h_transitive_l I hZF hH) hZF hω hSub hElem hωN
  have same {α β B R D V} (he : α = β) (hB : Entry_d M α B F) (hR : Entry_d M α R G)
      (hD : Entry_d M β D F) (hV : Entry_d M β V G) : Row_pil_d I α B R b D V N := by
    subst β
    have hBD := h.conditions.2.1.2 α B D hB hD
    have hRV := h.relations.2.1.2 α R V hR hV
    subst D; subst V
    exact row_pil_id_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) (h.stages α B R hB hR)
  let ρ : Env M 4 := (((⟨fun _ => F, fun _ => F⟩ : Env M 1).push G).push b).push N
  let φ : UnarySchema 4 := { body := row_pil_stage_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ β : φ.denote ρ β ↔ Row_pil_stage_d I F G b N β := row_pil_stage_sat_l I hZF.1 _ _ _ _ _ _
  apply hω.induction (fun β => Row_pil_stage_d I F G b N β)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨C, fun β => (hC β).trans (and_congr_right fun _ => hφ β)⟩
  · intro e he α B R D V _ hαe hB hR hD hV
    exact same (hZF.1.eq_of_same_members α e (fun x => iff_of_false (fun hx => he x (hαe x hx)) (he x))) hB hR hD hV
  · intro i hi ih β hβ α B R D V hαN hαβ hB hR hD hV
    have hαδ := (h.conditions.2.2 α).mpr ⟨B, hB⟩
    have hβδ := (h.conditions.2.2 β).mpr ⟨D, hD⟩
    have hiδ := h.conditions.1.transitive β hβδ i hβ.predecessor_mem
    rcases h.conditions.1.wellOrder.linear.compare α hαδ β hβδ with he | hαβ' | hβα
    · exact same (hZF.1.eq_of_same_members α β he) hB hR hD hV
    · have hαi : M.MemberSubset α i := by
        rcases (hβ α).mp hαβ' with hai | hai
        · exact (h.conditions.1.mem hiδ).transitive.memberSubset hai
        · exact fun x hx => (hai x).mp hx
      obtain ⟨C, hC⟩ := (h.conditions.2.2 i).mp hiδ
      obtain ⟨T, hT⟩ := (h.relations.2.2 i).mp hiδ
      exact row_pil_comp_l hZF hω hχ hH hJ hSub hElem (hωsub i hi) hαi
        (h.stages α B R hB hR) (h.stages i C T hC hT).order
        (h.links α i B R C T hB hR hC hT hαi)
        (h.links i β C T D V hC hT hD hV (fun x hx => (hβ x).mpr (Or.inl hx)))
        (ih α B R C T hαN hαi hB hR hC hT) (hn i β C T D V (hωsub i hi) hβ hC hT hD hV)
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) β (hαβ β hβα)).elim

end YesMetaZFC.Model.Forcing.Internal
