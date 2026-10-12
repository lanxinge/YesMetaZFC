import YesMetaZFC.Model.SetTheory.Internal.SubtypeProgramSyntax
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative

/-! # 子类型程序经共同根传递

把实际程序文本存在绑定后，留下的元数、长度、代码及七个槽位全是自然数。
两条完整初等图固定这些参数，所以目标取得同一码所约束的完整编译证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_program_in_d (ω n b z : M.Domain) (σ : Fin 7 → M.Domain) (C : M.Domain) : Prop :=
  let p : Fin 11 → M.Domain := fun i => [ω, n, b, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  (∀ i, M.mem (p i) C) ∧ Formula.satisfies ((⟨p, fun _ => ω⟩ : Env M 11).push C)
    (lr_rel_m ts_numeric0_m .newest (fun i => .bound i.succ))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω r B R x X S y Y T π σ C₀ C D : M.Domain}
  (nc : Nonempty {a // M.mem a C}) (ρ : Env (rt_model_l C nc) 12)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem ts_program_peer_l (hω : M.IsOmega ω)
    (bt : M.TransitiveSet B) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mb : Smem_d I r B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω r x B X π) (k : Smap_d I ω r y B Y σ) (hwB : M.mem ω B)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (ct : M.TransitiveSet C) (dt : M.TransitiveSet D) (hwD : M.mem ω D)
    (hw : p 0 = ω) (valid : Formula.satisfies ρ ts_program0_m) :
    Ts_program_in_d ω (p 1) (p 2) (p 4) (fun i => [p 5, p 6, p 7, p 8, p 9, p 10, p 11].get i) D := by
  have data := valid
  simp only [ts_program0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at data
  obtain ⟨hn, hb, hz, _, h₀, h₁, h₂, h₃, h₄, h₅, h₆, _⟩ := data
  have hwC : M.mem ω C := hw ▸ (ρ.bound 0).property
  let q : Fin 11 → M.Domain := fun i => [ω, p 1, p 2, p 4, p 5, p 6, p 7, p 8, p 9, p 10, p 11].get i
  have small a (ha : M.mem a (p 2)) := hω.transitive hZF (p 2) (hw ▸ hb) a ha
  have low : ∀ i, q i = ω ∨ M.mem (q i) ω := by
    simp only [Fin.forall_fin_succ]
    exact ⟨Or.inl rfl, Or.inr (hw ▸ hn), Or.inr (hw ▸ hb), Or.inr (hw ▸ hz),
      Or.inr (small _ h₀), Or.inr (small _ h₁), Or.inr (small _ h₂), Or.inr (small _ h₃),
      Or.inr (small _ h₄), Or.inr (small _ h₅), Or.inr (small _ h₆), fun i => Fin.elim0 i⟩
  have inC i : M.mem (q i) C := (low i).elim (fun eq => eq.symm ▸ hwC) (ct ω hwC _)
  have inD i : M.mem (q i) D := (low i).elim (fun eq => eq.symm ▸ hwD) (dt ω hwD _)
  let ξ : Env (rt_model_l C nc) 11 := ⟨fun i => ⟨q i, inC i⟩, fun _ => ⟨ω, hwC⟩⟩
  let nd : Nonempty {a // M.mem a D} := ⟨⟨ω, hwD⟩⟩
  let θ : Env (rt_model_l D nd) 11 := ⟨fun i => ⟨q i, inD i⟩, fun _ => ⟨ω, hwD⟩⟩
  have code : Formula.satisfies ξ ts_numeric0_m := by
    simp only [ts_numeric0_m, Formula.satisfies_exists_iff, ts_program_m, Formula.satisfies_bind]
    refine ⟨ρ.bound 3, (Formula.closed_env_l ts_program0_m ts_program0_closed_l ?_).mp valid⟩
    funext i
    exact Fin.cases (Subtype.ext hw) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  have moved := (smap_numeric_peer_l hZF hω bt xt yt mb mx my j k hwB iC iD ct dt nc nd
    ts_numeric0_m ts_numeric0_closed_l ξ θ (fun _ => rfl) low).mp code
  obtain ⟨c, H, model⟩ := smdl_membership_l I hZF ⟨ω, hwD⟩
  exact ⟨inD, (sc_relative_sat_l I model dt nd ts_numeric0_m ts_numeric0_closed_l θ
    ((⟨q, fun _ => ω⟩ : Env M 11).push D) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).mpr moved⟩

end YesMetaZFC.SetTheory.Internal
