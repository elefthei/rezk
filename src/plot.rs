use itertools::Itertools;
use std::fs::File;
use std::io::Result;
use std::process::Command;

use crate::nfa::NFA;

type Ed = (usize, String, usize);

impl<'a> dot::Labeller<'a, usize, Ed> for NFA {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("example").unwrap()
    }
    fn node_id(&'a self, n: &usize) -> dot::Id<'a> {
        // println!("EXPR: {:?}\n", self.expressions);
        dot::Id::new(format!("N{}", n)).unwrap()
    }
    fn node_label<'b>(&'b self, n: &usize) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr(format!("{}", self.expressions[n]).into())
    }
    fn node_style(&'a self, n: &usize) -> dot::Style {
        let init = self.get_init_state();
        let finals = self.get_final_states();
        if n == &init && finals.contains(&n) {
            dot::Style::Filled
        } else if finals.contains(&n) {
            dot::Style::Bold
        } else if n == &init {
            dot::Style::Dashed
        } else {
            dot::Style::None
        }
    }

    fn edge_label<'b>(&'b self, e: &Ed) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr(format!("{}", e.1).into())
    }
}

impl<'a> dot::GraphWalk<'a, usize, Ed> for NFA {
    fn nodes(&'a self) -> dot::Nodes<'a, usize> {
        (0..self.n).collect()
    }
    fn edges(&'a self) -> dot::Edges<'a, Ed> {
        self.trans
            .clone()
            .into_iter()
            .map(|((a, c), b)| ((a, b), c))
            .into_group_map()
            .into_iter()
            .map(|((a, b), c)| {
                (
                    a,
                    if c.len() > 6 && c.len() > self.ab.len()/4 {
                        "*".to_string()
                    } else {
                        c.join(", ").trim().to_string()
                    },
                    b,
                )
            })
            .collect()
    }

    fn source(&self, e: &Ed) -> usize {
        e.0
    }
    fn target(&self, e: &Ed) -> usize {
        e.2
    }
}

pub trait Plottable {
    fn plot(&self, fin: &str) -> Result<()>;
}

impl Plottable for NFA {
    fn plot(&self, fin: &str) -> Result<()> {
        let filename = fin.to_string();
        let dotfile = filename.clone() + ".dot";
        let pdffile = filename + ".pdf";

        // Output file
        let mut buffer = File::create(&dotfile).unwrap();

        // render .dot file
        dot::render(self, &mut buffer).unwrap();
        println!("Wrote DOT file {}.", &dotfile);

        // Convert to pdf
        Command::new("dot")
            .arg("-Tpdf")
            .arg(dotfile)
            .arg("-o")
            .arg(pdffile)
            .spawn()
            .expect("[dot] CLI failed to convert nfa to [pdf] file")
            .wait()?;
        Ok(())
    }
}

impl Plottable for Vec<NFA> {
    fn plot(&self, fin: &str) -> Result<()> {
        let filename = fin.to_string();
        let dotfiles = (0..self.len()).map(|i| filename.to_owned() + &i.to_string() + ".dot");
        let pdffiles = (0..self.len()).map(|i| filename.to_owned() + &i.to_string() + ".pdf");
        let end_pdf = filename.to_owned() + ".pdf";

        self.into_iter()
            .enumerate()
            .try_for_each(|(i, nfa)| nfa.plot(&(filename.clone() + &i.to_string())))?;

        Command::new("pdfjam")
            .args(pdffiles.clone())
            .arg("-o")
            .arg(end_pdf)
            .spawn()
            .expect("[pdfjam] CLI failed to concatenate pdf files")
            .wait()?;

        for f in dotfiles.into_iter().chain(pdffiles.into_iter()) {
            std::fs::remove_file(f)?;
        }
        Ok(())
    }
}

