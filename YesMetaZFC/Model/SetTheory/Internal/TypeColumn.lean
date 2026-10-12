import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 原变量前缀与有限参数表的统一名字列

内部 n 个变量保持原位置；固定模板的参数逐项追加。返回实际槽位表供
程序编译与名字求值共同使用，不依赖 n 在外部是否标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_column_append_l {f l m N x : M.Domain} (hl : M.IsOrdinal l) (hs : M.SuccessorOf m l)
    (hf : M.IsSetFunctionFromTo I f l N) (hx : M.mem x N) :
    ∃ g, M.IsSetFunctionFromTo I g m N ∧
      (∀ i y, M.mem i l → (Rd_entry_d i y g ↔ Rd_entry_d i y f)) ∧ Rd_entry_d l x g := by
  obtain ⟨g, hg, graph⟩ := Structure.IsSequenceOfLength.exists_append (ZF.modelsKP hZF) I ⟨hl, hf.1, hf.2.1⟩
    (KP.successor_isOrdinal (ZF.modelsKP hZF) hl hs) hs
  have bound i y (h : Rd_entry_d i y g) : M.mem y N :=
    ((graph i y).mp h).elim (fun h => hf.output_mem_of_pairMember h) (fun h => h.2.symm ▸ hx)
  exact ⟨g, ⟨hg.2.1, hg.2.2, fun i hi => ((hg.2.2 i).mp hi).imp fun y hy => ⟨bound i y hy, hy⟩⟩,
    fun i y hi => (graph i y).trans ⟨fun h => h.elim id (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZF) l (h.1 ▸ hi)).elim), Or.inl⟩,
    (graph l x).mpr (Or.inr ⟨rfl, rfl⟩)⟩

theorem tt_column_build_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) (k : Nat) :
    ∃ b, ∃ σ : Fin k → M.Domain, M.mem b ω ∧ M.MemberSubset n b ∧ (∀ i, M.mem (σ i) b) ∧
      (∀ i, M.mem i b → M.mem i n ∨ ∃ j, i = σ j) ∧
      ∀ U N, Tn_names_d n U N → ∀ a : Fin k → M.Domain, (∀ i, M.mem (a i) N) →
        ∃ C, M.IsSetFunctionFromTo I C b N ∧ (∀ i, M.mem i n → Rd_entry_d i i C) ∧
          ∀ i, Rd_entry_d (σ i) (a i) C := by
  induction k with
  | zero =>
    refine ⟨n, Fin.elim0, hn, fun _ h => h, fun i => Fin.elim0 i,
      fun _ h => Or.inl h, fun U N names a ha => ?_⟩
    let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
    let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
    have sat i x : φ.denote ρ i x ↔ x = i := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
    obtain ⟨C, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := N)
      (fun i _ => ⟨i, (sat i i).mpr rfl⟩)
      (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
      (fun i x hi hx => ((sat i x).mp hx).symm ▸ (names i).mpr (Or.inl hi))
    exact ⟨C, fn, fun i hi => (graph i i).mpr ⟨hi, (sat i i).mpr rfl⟩, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨b, σ, hb, nb, bound, cover, build⟩ := ih
    obtain ⟨d, hd, hdω⟩ := hω.1.2 b hb
    refine ⟨d, Fin.cases b σ, hdω, fun i hi => (hd i).mpr (Or.inl (nb i hi)),
      Fin.cases hd.predecessor_mem (fun i => (hd (σ i)).mpr (Or.inl (bound i))), ?_, fun U N names a ha => ?_⟩
    · intro i hi
      rcases (hd i).mp hi with hi | hi
      · exact (cover i hi).elim Or.inl (fun ⟨j, hj⟩ => Or.inr ⟨j.succ, hj⟩)
      · exact Or.inr ⟨0, hZF.1.eq_of_same_members i b hi⟩
    obtain ⟨C, fn, old, values⟩ := build U N names (fun i => a i.succ) (fun i => ha i.succ)
    obtain ⟨C', fn', kept, last⟩ := tt_column_append_l hZF (hω.members_areOrdinals hZF b hb) hd fn (ha 0)
    exact ⟨C', fn',
      fun i hi => (kept i i (nb i hi)).mpr (old i hi),
      Fin.cases last (fun i => (kept (σ i) (a i.succ) (bound i)).mpr (values i))⟩

end YesMetaZFC.SetTheory.Internal
