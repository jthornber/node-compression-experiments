use clap::builder::{PossibleValuesParser, TypedValueParser};
use clap::{value_parser, Arg, ArgAction};
use std::path::Path;

use thinp::commands::engine::*;
use thinp::commands::utils::*;
use thinp::report::*;
use thinp::thin::metadata_repair::SuperblockOverrides;
use thinp::version::*;

use node_compression_experiments::dump::*;

//----------------------------------------------------------------

pub struct ThinDumpCommand;

impl ThinDumpCommand {
    fn cli(&self) -> clap::Command {
        let cmd = clap::Command::new("encode")
            .next_display_order(None)
            .disable_version_flag(true)
            .arg(
                Arg::new("DEV_ID")
                    .help("Dump the specified device")
                    .long("dev-id")
                    .action(clap::ArgAction::Append)
                    .value_name("THIN_ID")
                    .value_parser(value_parser!(u64)),
            )
            .arg(
                Arg::new("OUTPUT")
                    .help("Specify the output file rather than stdout")
                    .short('o')
                    .long("output")
                    .value_name("FILE"),
            )
            .arg(
                Arg::new("INPUT")
                    .help("Specify the input device to dump")
                    .required(true)
                    .index(1),
            );
        verbose_args(engine_args(version_args(cmd)))
    }

    fn run(&self, args: &mut dyn Iterator<Item = std::ffi::OsString>) -> exitcode::ExitCode {
        let matches = self.cli().get_matches_from(args);
        display_version(&matches);

        let input_file = Path::new(matches.get_one::<String>("INPUT").unwrap());
        let output_file = matches.get_one::<String>("OUTPUT").map(Path::new);

        let report = mk_report(false);
        let log_level = match parse_log_level(&matches) {
            Ok(level) => level,
            Err(e) => return to_exit_code::<()>(&report, Err(anyhow::Error::msg(e))),
        };
        report.set_level(log_level);

        if let Err(e) = check_input_file(input_file).and_then(check_file_not_tiny) {
            return to_exit_code::<()>(&report, Err(e));
        }

        let engine_opts = parse_engine_opts(ToolType::Thin, &matches);
        if engine_opts.is_err() {
            return to_exit_code(&report, engine_opts);
        }

        let selected_devs: Option<Vec<u64>> = matches
            .get_many::<u64>("DEV_ID")
            .map(|devs| devs.copied().collect());

        let opts = ThinDumpOptions {
            input: input_file,
            output: output_file,
            engine_opts: engine_opts.unwrap(),
            report: report.clone(),
        };

        to_exit_code(&report, dump(opts))
    }
}

fn main() {
    let dumper = ThinDumpCommand {};
    let mut args = std::env::args_os().peekable();
    dumper.run(&mut args);
}
